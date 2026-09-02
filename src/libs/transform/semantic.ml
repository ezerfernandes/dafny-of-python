open Base

open Pyparse.Astpy
open Pyparse.Sourcemap

(* Semantic information is deliberately kept separate from the syntax tree.
   The parser represents annotations with specialised constructors (TLst,
   TDict, ...), while all later passes can use the single TGeneric form. *)

type callable_kind = PureFunction | Method | Constructor | Generator

exception SemanticError of string

let fail message = raise (SemanticError message)

type callable_signature =
  { name : string
  ; parameters : (string * typ) list
  ; return_type : typ
  ; kind : callable_kind
  }

type field =
  { field_name : string
  ; field_type : typ
  }

type class_definition =
  { class_name : string
  ; fields : field list
  ; methods : callable_signature list
  }

type scope_kind = Global | FunctionScope of string | ClassScope of string | ComprehensionScope

type scope =
  { kind : scope_kind
  ; bindings : (string * typ) list
  }

type environment =
  { scopes : scope list
  ; functions : callable_signature list
  ; classes : class_definition list
  ; memberships : (string * string) list
  ; known_map_keys : (string * string list) list
  ; map_aliases : string list
  ; list_aliases : (string * string) list
  ; iterated_lists : string list
  }

let empty =
  { scopes = [ { kind = Global; bindings = [] } ]
  ; functions = []
  ; classes = []
  ; memberships = []
  ; known_map_keys = []
  ; map_aliases = []
  ; list_aliases = []
  ; iterated_lists = []
  }

let generic name args = TGeneric ((def_pos, Some name), args)

let segment_name segment =
  match snd segment with
  | Some name -> String.lowercase name
  | None -> ""

let rec normalize_type = function
  | TIdent segment as typ ->
    begin
      match segment_name segment with
      | "list" -> generic "list" []
      | "seq" | "sequence" -> generic "seq" []
      | "set" -> generic "set" []
      | "dict" | "map" -> generic "map" []
      | "tuple" -> generic "tuple" []
      | "array" -> generic "array" []
      | _ -> typ
    end
  | TLst (_, element) ->
    generic "list" (Option.to_list element |> List.map ~f:normalize_type)
  | TDict (_, key, value) ->
    let args = Option.to_list key @ Option.to_list value in
    generic "map" (List.map args ~f:normalize_type)
  | TSet (_, element) ->
    generic "set" (Option.to_list element |> List.map ~f:normalize_type)
  | TTuple (_, Some [ element ]) -> normalize_type element
  | TTuple (_, elements) ->
    generic "tuple"
      (Option.value_map elements ~default:[] ~f:(List.map ~f:normalize_type))
  | TCallable (segment, parameters, result) ->
    TCallable (segment, List.map parameters ~f:normalize_type, normalize_type result)
  | TType (_, element) ->
    generic "type" (Option.to_list element |> List.map ~f:normalize_type)
  | TGeneric (segment, arguments) ->
    begin
      match segment_name segment, arguments with
      | "tuple", [ element ] -> normalize_type element
      | _, _ -> TGeneric (segment, List.map arguments ~f:normalize_type)
    end
  | typ -> typ

let rec normalize_param (identifier, annotation_expression) =
  identifier, normalize_exp annotation_expression

and normalize_exp = function
  | Typ typ -> Typ (normalize_type typ)
  | Literal _ as expression -> expression
  | Identifier _ as expression -> expression
  | Dot (value, identifier) -> Dot (normalize_exp value, identifier)
  | BinaryExp (left, operator, right) ->
    BinaryExp (normalize_exp left, operator, normalize_exp right)
  | CompareChain (first, comparisons) ->
    CompareChain
      ( normalize_exp first
      , List.map comparisons ~f:(fun (operator, operand) -> operator, normalize_exp operand) )
  | UnaryExp (operator, value) -> UnaryExp (operator, normalize_exp value)
  | Call (callee, arguments) -> Call (normalize_exp callee, List.map arguments ~f:normalize_exp)
  | Lst elements -> Lst (List.map elements ~f:normalize_exp)
  | Array elements -> Array (List.map elements ~f:normalize_exp)
  | Set elements -> Set (List.map elements ~f:normalize_exp)
  | Dict entries ->
    Dict (List.map entries ~f:(fun (key, value) -> normalize_exp key, normalize_exp value))
  | Tuple [] -> fail "empty tuples are unsupported"
  | Tuple [ element ] -> normalize_exp element
  | Tuple elements -> Tuple (List.map elements ~f:normalize_exp)
  | SingletonTuple (_, element) -> normalize_exp element
  | Subscript (value, selector) -> Subscript (normalize_exp value, normalize_exp selector)
  | Index value -> Index (normalize_exp value)
  | Slice (lower_bound, upper_bound) ->
    Slice (Option.map lower_bound ~f:normalize_exp, Option.map upper_bound ~f:normalize_exp)
  | Forall (identifiers, body) -> Forall (identifiers, normalize_exp body)
  | Exists (identifiers, body) -> Exists (identifiers, normalize_exp body)
  | Len (segment, value) -> Len (segment, normalize_exp value)
  | Max (segment, value) -> Max (segment, normalize_exp value)
  | Old (segment, value) -> Old (segment, normalize_exp value)
  | Fresh (segment, value) -> Fresh (segment, normalize_exp value)
  | Lambda (identifiers, body) -> Lambda (identifiers, normalize_exp body)
  | IfElseExp (when_true, condition, when_false) ->
    IfElseExp (normalize_exp when_true, normalize_exp condition, normalize_exp when_false)

let normalize_spec = function
  | Pre value -> Pre (normalize_exp value)
  | Post value -> Post (normalize_exp value)
  | Invariant value -> Invariant (normalize_exp value)
  | Decreases value -> Decreases (normalize_exp value)
  | Reads value -> Reads (normalize_exp value)
  | Modifies value -> Modifies (normalize_exp value)

let rec normalize_statement = function
  | IfElse (condition, first, alternatives, last) ->
    IfElse
      ( normalize_exp condition
      , List.map first ~f:normalize_statement
      , List.map alternatives ~f:(fun (condition, body) ->
          normalize_exp condition, List.map body ~f:normalize_statement)
      , List.map last ~f:normalize_statement )
  | For (specifications, identifiers, iterable, body) ->
    For
      ( List.map specifications ~f:normalize_spec
      , identifiers
      , normalize_exp iterable
      , List.map body ~f:normalize_statement )
  | While (specifications, condition, body) ->
    While
      ( List.map specifications ~f:normalize_spec
      , normalize_exp condition
      , List.map body ~f:normalize_statement )
  | Assign (annotation, targets, values) ->
    Assign
      ( Option.map annotation ~f:normalize_exp
      , List.map targets ~f:normalize_exp
      , List.map values ~f:normalize_exp )
  | Function (specifications, name, parameters, return_type, body) ->
    Function
      ( List.map specifications ~f:normalize_spec
      , name
      , List.map parameters ~f:normalize_param
      , normalize_exp return_type
      , List.map body ~f:normalize_statement )
  | Return value -> Return (normalize_exp value)
  | Assert value -> Assert (normalize_exp value)
  | Exp value -> Exp (normalize_exp value)
  | (Break | Continue | Pass) as statement -> statement

let normalize_program (Program statements) =
  Program (List.map statements ~f:normalize_statement)

let type_name typ =
  match typ with
  | TLst _ -> "list"
  | TDict _ -> "map"
  | TSet _ -> "set"
  | TTuple _ -> "tuple"
  | TType _ -> "type"
  | TGeneric (segment, _) -> segment_name segment
  | TIdent segment -> segment_name segment
  | TInt _ -> "int"
  | TFloat _ -> "float"
  | TBool _ -> "bool"
  | TStr _ -> "str"
  | TNone _ -> "none"
  | TObj _ -> "object"
  | TCallable _ -> "callable"

let generic_arguments typ =
  match normalize_type typ with
  | TGeneric (_, arguments) -> arguments
  | _ -> []

type collection_kind =
  | ListCollection
  | SequenceCollection
  | ArrayCollection
  | SetCollection
  | MapCollection
  | TupleCollection
  | StringCollection
  | UnknownCollection
  | NonCollection

let collection_kind typ =
  match normalize_type typ with
  | TGeneric (segment, _) ->
    begin
      match segment_name segment with
      | "list" -> ListCollection
      | "seq" -> SequenceCollection
      | "array" -> ArrayCollection
      | "set" -> SetCollection
      | "map" -> MapCollection
      | "tuple" -> TupleCollection
      | _ -> UnknownCollection
    end
  | TStr _ -> StringCollection
  | TIdent _ -> UnknownCollection
  | _ -> NonCollection

let collection_arguments typ = generic_arguments typ

let collection_element_type typ =
  match collection_kind typ, collection_arguments typ with
  | (ListCollection | SequenceCollection | ArrayCollection | SetCollection), element :: _ -> Some element
  | TupleCollection, [] -> None
  | TupleCollection, first :: rest ->
    Some (List.fold rest ~init:first ~f:(fun common element ->
      if eqtyp common element then common else TIdent def_seg))
  | _ -> None

let map_types typ =
  match collection_kind typ, collection_arguments typ with
  | MapCollection, key :: value :: _ -> Some (key, value)
  | _ -> None

let set_source_element_type typ =
  match collection_kind typ with
  | MapCollection -> Option.map (map_types typ) ~f:fst
  | _ -> collection_element_type typ

let identifier_name = function
  | Identifier segment -> Option.value (snd segment) ~default:""
  | _ -> ""

let list_alias_root env name =
  Option.value (List.Assoc.find env.list_aliases name ~equal:String.equal) ~default:name

let list_aliases_for env name =
  let root = list_alias_root env name in
  let names =
    List.fold env.list_aliases ~init:[ root ] ~f:(fun names (alias, alias_root) ->
      if String.equal alias_root root
         && not (List.exists names ~f:(String.equal alias))
      then alias :: names
      else names)
  in
  List.rev names

let literal_key = function
  | Literal (IntLit value) -> Some ("int:" ^ value)
  | Literal (FloatLit value) -> Some ("float:" ^ value)
  | Literal (StringLit value) -> Some ("string:" ^ value)
  | Literal TrueLit -> Some "bool:true"
  | Literal FalseLit -> Some "bool:false"
  | Literal NoneLit -> Some "none"
  | _ -> None

let map_keys env name =
  Option.value (List.Assoc.find env.known_map_keys name ~equal:String.equal) ~default:[]

let set_map_keys env name keys =
  let known_map_keys =
    (name, keys) :: List.Assoc.remove env.known_map_keys name ~equal:String.equal
  in
  { env with known_map_keys }

let add_membership env key map =
  if String.is_empty key || String.is_empty map then env
  else { env with memberships = (key, map) :: List.filter env.memberships ~f:(fun (old_key, old_map) -> not (String.equal old_key key && String.equal old_map map)) }

let has_membership env key map =
  List.exists env.memberships ~f:(fun (old_key, old_map) -> String.equal old_key key && String.equal old_map map)

let membership_assumption = function
  | BinaryExp (Identifier key, (In _), Identifier map) -> Some (identifier_name (Identifier key), identifier_name (Identifier map))
  | CompareChain (Identifier key, [ (In _, Identifier map) ]) -> Some (identifier_name (Identifier key), identifier_name (Identifier map))
  | _ -> None

let assume_membership env expression =
  match membership_assumption expression with
  | Some (key, map) -> add_membership env key map
  | None -> env

let rec find_binding name = function
  | [] -> None
  | scope :: rest ->
    begin
      match List.Assoc.find scope.bindings ~equal:String.equal name with
      | Some typ -> Some typ
      | None -> find_binding name rest
    end

let lookup env name = find_binding name env.scopes

let lookup_function env name =
  List.find env.functions ~f:(fun signature -> String.equal signature.name name)

let lookup_class env name =
  let name = String.lowercase name in
  List.find env.classes ~f:(fun definition -> String.equal (String.lowercase definition.class_name) name)

let callable_type signature =
  TCallable
    ((def_pos, Some signature.name), List.map signature.parameters ~f:snd, signature.return_type)

let bind env name typ =
  match env.scopes with
  | [] -> env
  | scope :: rest ->
    let bindings = (name, normalize_type typ) :: List.Assoc.remove scope.bindings name ~equal:String.equal in
    { env with
      scopes = { scope with bindings } :: rest
    ; known_map_keys = List.Assoc.remove env.known_map_keys name ~equal:String.equal
    ; map_aliases = List.filter env.map_aliases ~f:(fun old -> not (String.equal old name))
    ; list_aliases =
        List.filter env.list_aliases ~f:(fun (alias, source) ->
          not (String.equal alias name || String.equal source name))
    ; iterated_lists = List.filter env.iterated_lists ~f:(fun old -> not (String.equal old name))
    }

let bind_many env bindings =
  List.fold bindings ~init:env ~f:(fun env (name, typ) -> bind env name typ)

let bind_value env name typ value =
  let env = bind env name typ in
  let keys =
    match value with
    | Dict entries -> List.filter_map entries ~f:(fun (key, _) -> literal_key key)
    | _ -> []
  in
  let env = set_map_keys env name keys in
  match value, collection_kind typ with
  | Identifier _, MapCollection ->
    { env with map_aliases = name :: env.map_aliases }
  | Identifier source, ListCollection
    when not (String.equal name (identifier_name (Identifier source))) ->
    let source = list_alias_root env (identifier_name value) in
    { env with list_aliases = (name, source) :: env.list_aliases }
  | _ -> env

let add_map_key env name key =
  match literal_key key with
  | None -> env
  | Some key ->
    set_map_keys env name
      (key :: List.filter (map_keys env name) ~f:(fun old -> not (String.equal old key)))

let enter_scope env kind = { env with scopes = { kind; bindings = [] } :: env.scopes }

let leave_scope env =
  match env.scopes with
  | _ :: rest -> { env with scopes = rest }
  | [] -> env

let add_function env signature =
  let functions = signature :: List.filter env.functions ~f:(fun old -> not (String.equal old.name signature.name)) in
  { env with functions }

let add_class env definition =
  let classes = definition :: List.filter env.classes ~f:(fun old -> not (String.equal old.class_name definition.class_name)) in
  { env with classes }

let annotation = function
  | Typ typ -> normalize_type typ
  | Identifier segment -> normalize_type (TIdent segment)
  | _ -> TIdent def_seg

let infer_literal = function
  | TrueLit | FalseLit -> TBool def_seg
  | IntLit _ -> TInt def_seg
  | FloatLit _ -> TFloat def_seg
  | StringLit _ -> TStr def_seg
  | NoneLit -> TNone def_seg

let numeric_type left right =
  match normalize_type left, normalize_type right with
  | TFloat _, _ | _, TFloat _ -> TFloat def_seg
  | TInt _, TInt _ -> TInt def_seg
  | _ -> TIdent def_seg

let rec tuple_element index = function
  | [] -> TIdent def_seg
  | typ :: _ when index = 0 -> typ
  | _ :: rest -> tuple_element (index - 1) rest

let integer_literal = function
  | Literal (IntLit value) -> (try Some (Int.of_string value) with _ -> None)
  | _ -> None

let rec infer env = function
  | Typ typ -> normalize_type typ
  | Literal literal -> infer_literal literal
  | Identifier segment ->
    begin
      match lookup env (Option.value (snd segment) ~default:"") with
      | Some typ -> typ
      | None ->
        begin
          match lookup_function env (Option.value (snd segment) ~default:"") with
          | Some signature -> TCallable (segment, List.map signature.parameters ~f:snd, signature.return_type)
          | None -> TIdent segment
        end
    end
  | Dot (value, field_name) ->
    begin
      match normalize_type (infer env value) with
      | TGeneric (class_segment, _) ->
        begin
          match lookup_class env (segment_name class_segment) with
          | Some definition ->
            begin
              match List.find definition.fields ~f:(fun field -> String.equal field.field_name (Option.value (snd field_name) ~default:"")) with
              | Some field -> field.field_type
              | None ->
                begin
                  match List.find definition.methods ~f:(fun method_ -> String.equal method_.name (Option.value (snd field_name) ~default:"")) with
                  | Some method_ -> callable_type method_
                  | None -> TIdent field_name
                end
            end
          | None -> TIdent field_name
        end
      | _ -> TIdent field_name
    end
  | UnaryExp (_, value) -> infer env value
  | BinaryExp (left, operator, right) ->
    begin
      match operator with
      | EqEq _ | NEq _ | Lt _ | LEq _ | Gt _ | GEq _ | And _ | Or _
      | NotIn _ | In _ | BiImpl _ | Implies _ | Explies _ -> TBool def_seg
      | Plus _ | Minus _ | Times _ | Divide _ | Mod _ -> numeric_type (infer env left) (infer env right)
      | BitOr _ | BitAnd _ -> infer env left
    end
  | CompareChain _ -> TBool def_seg
  | SingletonTuple (_, value) -> infer env value
  | Call (callee, arguments) ->
    begin
      match callee with
      | Identifier segment ->
        begin
          match Option.value (snd segment) ~default:"" |> String.lowercase with
          | "len" -> TInt def_seg
          | "list" ->
            let element = match arguments with
              | [ Lst elements ] -> List.find_map elements ~f:(fun element -> Some (infer env element))
              | _ -> None
            in
            generic "list" (Option.to_list element)
          | "set" | "setf" ->
            begin
              match arguments with
              | [ argument ] ->
                generic "set" (Option.to_list (set_source_element_type (infer env argument)))
              | _ -> generic "set" []
            end
          | "dict" | "dictf" | "map" -> generic "map" []
          | _ ->
            begin
              match lookup_function env (Option.value (snd segment) ~default:"") with
              | Some signature -> signature.return_type
              | None -> TIdent def_seg
            end
        end
      | Dot (value, field_name) ->
        begin
          match infer env (Dot (value, field_name)) with
          | TCallable (_, _, return_type) -> return_type
          | _ -> TIdent def_seg
        end
      | _ -> TIdent def_seg
    end
  | Lst elements ->
    let element = List.find_map elements ~f:(fun element -> Some (infer env element)) in
    generic "list" (Option.to_list element)
  | Array elements ->
    let element = List.find_map elements ~f:(fun element -> Some (infer env element)) in
    generic "array" (Option.to_list element)
  | Set elements ->
    let element = List.find_map elements ~f:(fun element -> Some (infer env element)) in
    generic "set" (Option.to_list element)
  | Dict entries ->
    let key, value =
      match List.find_map entries ~f:(fun (key, value) -> Some (infer env key, infer env value)) with
      | Some pair -> pair
      | None -> TIdent def_seg, TIdent def_seg
    in
    generic "map" [ key; value ]
  | Tuple elements -> generic "tuple" (List.map elements ~f:(infer env))
  | Subscript (value, selector) ->
    begin
      match normalize_type (infer env value), selector with
      | TGeneric (segment, [ element ]), Index _
        when String.equal (segment_name segment) "list"
          || String.equal (segment_name segment) "array"
          || String.equal (segment_name segment) "seq" -> element
      | TGeneric (segment, [ _; value_type ]), Index _
        when String.equal (segment_name segment) "map" -> value_type
      | TGeneric (segment, elements), Index index
        when String.equal (segment_name segment) "tuple" ->
        Option.value_map (integer_literal index) ~default:(TIdent def_seg)
          ~f:(fun position -> tuple_element position elements)
      | _ -> TIdent def_seg
    end
  | Index value -> infer env value
  | Slice (lower, upper) ->
    Option.value_map lower ~default:(Option.value_map upper ~default:(TInt def_seg) ~f:(infer env)) ~f:(infer env)
  | Forall (identifiers, body) | Exists (identifiers, body) ->
    let scoped = enter_scope env ComprehensionScope in
    let scoped = bind_many scoped (List.map identifiers ~f:(fun identifier -> Option.value (snd identifier) ~default:"", TIdent identifier)) in
    ignore (infer scoped body);
    TBool def_seg
  | Len (_, _) -> TInt def_seg
  | Max (_, value) ->
    begin
      match generic_arguments (infer env value) with
      | element :: _ -> element
      | [] -> TIdent def_seg
    end
  | Old (_, value) | Fresh (_, value) -> infer env value
  | Lambda (identifiers, body) ->
    let scoped = enter_scope env (FunctionScope "lambda") in
    let scoped = bind_many scoped (List.map identifiers ~f:(fun identifier -> Option.value (snd identifier) ~default:"", TIdent identifier)) in
    let result = infer scoped body in
    TCallable (def_seg, List.map identifiers ~f:(fun _ -> TIdent def_seg), result)
  | IfElseExp (when_true, condition, when_false) ->
    ignore (infer env condition);
    let true_type = infer env when_true in
    let false_type = infer env when_false in
    if subtyp true_type false_type then false_type
    else if subtyp false_type true_type then true_type
    else TIdent def_seg

let callable_kind env callee =
  match callee with
  | Identifier segment ->
    begin
      match lookup_function env (Option.value (snd segment) ~default:"") with
      | Some signature -> signature.kind
      | None -> PureFunction
    end
  | Dot _ -> Method
  | _ -> PureFunction

let rec type_of_target env = function
  | Identifier identifier -> lookup env (Option.value (snd identifier) ~default:"") |> Option.value ~default:(TIdent identifier)
  | Dot (value, field_name) -> infer env (Dot (value, field_name))
  | Subscript (value, selector) -> infer env (Subscript (value, selector))
  | Tuple [ target ] -> type_of_target env target
  | Tuple targets -> generic "tuple" (List.map targets ~f:(type_of_target env))
  | _ -> TIdent def_seg

let function_signature name parameters return_type =
  { name = Option.value (snd name) ~default:""
  ; parameters = List.map parameters ~f:(fun (identifier, value) -> Option.value (snd identifier) ~default:"", annotation value)
  ; return_type = annotation return_type
  ; kind = PureFunction
  }

let rec collect_functions env statements =
  List.fold statements ~init:env ~f:(fun env statement ->
    match statement with
    | Function (_, name, parameters, return_type, body) ->
      let env = add_function env (function_signature name parameters return_type) in
      collect_functions env body
    | IfElse (_, first, alternatives, last) ->
      let env = collect_functions env first in
      let env = List.fold alternatives ~init:env ~f:(fun env (_, body) -> collect_functions env body) in
      collect_functions env last
    | While (_, _, body) | For (_, _, _, body) -> collect_functions env body
    | _ -> env)

let rec collect_function_bodies statements =
  List.concat_map statements ~f:(fun statement ->
    match statement with
    | Function (_, name, _, _, body) ->
      (identifier_name (Identifier name), body) :: collect_function_bodies body
    | IfElse (_, first, alternatives, last) ->
      collect_function_bodies first
      @ List.concat_map alternatives ~f:(fun (_, body) -> collect_function_bodies body)
      @ collect_function_bodies last
    | While (_, _, body) | For (_, _, _, body) -> collect_function_bodies body
    | _ -> [])

(* A function body with a statement sequence, a list construction, or a call
   to a method cannot be emitted as a Dafny function.  Keep this information
   in the callable environment before lowering any callers. *)
let rec expression_needs_method env = function
  | Typ _ | Literal _ | Identifier _ -> false
  | Dot (value, _) -> expression_needs_method env value
  | BinaryExp (left, _, right) ->
    expression_needs_method env left || expression_needs_method env right
  | CompareChain (first, comparisons) ->
    expression_needs_method env first
    || List.exists comparisons ~f:(fun (_, operand) -> expression_needs_method env operand)
  | UnaryExp (_, value) -> expression_needs_method env value
  | Call (callee, arguments) ->
    expression_needs_method env callee
    || List.exists arguments ~f:(expression_needs_method env)
    || begin
      match callee with
      | Dot _ -> true
      | Identifier identifier ->
        begin
          match lookup_function env (Option.value (snd identifier) ~default:"") with
          | Some { kind = PureFunction; _ } | None -> false
          | Some _ -> true
        end
      | _ -> false
    end
  | Lst elements ->
    (* The runtime List representation requires a statement-level
       construction, even when its elements are all pure. *)
    ignore elements;
    true
  | Array elements | Set elements | Tuple elements ->
    List.exists elements ~f:(expression_needs_method env)
  | Dict entries ->
    List.exists entries ~f:(fun (key, value) ->
      expression_needs_method env key || expression_needs_method env value)
  | SingletonTuple (_, value) -> expression_needs_method env value
  | Subscript (value, selector) ->
    expression_needs_method env value
    || expression_needs_method env selector
    || begin
      match selector, collection_kind (infer env value) with
      | Slice _, ListCollection -> true
      | _ -> false
    end
  | Index value -> expression_needs_method env value
  | Slice (lower, upper) ->
    Option.exists lower ~f:(expression_needs_method env)
    || Option.exists upper ~f:(expression_needs_method env)
  | Forall (_, body) | Exists (_, body) -> expression_needs_method env body
  | Len (_, value) | Max (_, value) | Old (_, value) | Fresh (_, value) ->
    expression_needs_method env value
  | Lambda (_, body) -> expression_needs_method env body
  | IfElseExp (when_true, condition, when_false) ->
    expression_needs_method env when_true
    || expression_needs_method env condition
    || expression_needs_method env when_false

let function_needs_method env body =
  match body with
  | [ Return expression ] | [ Exp expression ] -> expression_needs_method env expression
  | [ Pass ] -> false
  | _ -> true

let classify_functions env statements =
  let bodies = collect_function_bodies statements in
  let rec fixpoint env =
    let changed = ref false in
    let env =
      List.fold bodies ~init:env ~f:(fun env (name, body) ->
        match lookup_function env name with
        | Some signature ->
          let function_environment = enter_scope env (FunctionScope signature.name) in
          let function_environment = bind_many function_environment signature.parameters in
          if function_needs_method function_environment body then
          begin
            match signature.kind with
            | PureFunction ->
              changed := true;
              add_function env { signature with kind = Method }
            | _ -> env
          end
          else env
        | None -> env)
    in
    if !changed then fixpoint env else env
  in
  fixpoint env

let is_unknown_type typ =
  match normalize_type typ with
  | TIdent _ -> true
  | _ -> false

let compatible_types left right =
  is_unknown_type left || is_unknown_type right || eqtyp (normalize_type left) (normalize_type right)

let require condition message = if not condition then fail message

let require_compatible left right message = require (compatible_types left right) message

let rec is_hashable_type typ =
  match typ with
  | TType (_, Some typ) -> is_hashable_type typ
  | _ ->
    match normalize_type typ with
    | TInt _ | TFloat _ | TBool _ | TStr _ | TNone _ -> true
    | TGeneric (segment, arguments) ->
      begin
        match segment_name segment, arguments with
        | "tuple", arguments -> List.for_all arguments ~f:is_hashable_type
        | "list", _ | "set", _ | "map", _ | "array", _ | "seq", _ -> false
        | _, _ -> false
      end
    | _ -> false

let require_hashable typ message = require (is_hashable_type typ) message

let list_mutating_methods =
  [ "append"; "insert"; "remove"; "pop"; "clear"; "reverse"; "sort"; "extend" ]

let is_list_mutating_method name =
  List.mem list_mutating_methods (String.lowercase name) ~equal:String.equal

let require_set_elements left right message =
  match collection_element_type left, collection_element_type right with
  | Some left, Some right -> require_compatible left right message
  | _ -> fail "set operation requires a concrete element type"

let require_collection kind message =
  require
    (match kind with
     | UnknownCollection | ListCollection | SequenceCollection | ArrayCollection
     | SetCollection | MapCollection | TupleCollection | StringCollection -> true
     | NonCollection -> false)
    message

let require_set_source kind message =
  require
    (match kind with
     | ListCollection | SequenceCollection | SetCollection | MapCollection -> true
     | _ -> false)
    message

let membership_type _env value_type =
  match collection_kind value_type, collection_arguments value_type with
  | SetCollection, element :: _ -> Some element
  | MapCollection, key :: _ -> Some key
  | ListCollection, element :: _ -> Some element
  | SequenceCollection, element :: _ -> Some element
  | ArrayCollection, element :: _ -> Some element
  | TupleCollection, elements ->
    begin
      match elements with
      | [] -> None
      | first :: rest -> Some (List.fold rest ~init:first ~f:(fun common element ->
          if compatible_types common element then common else TIdent def_seg))
    end
  | StringCollection, _ -> Some (TStr def_seg)
  | UnknownCollection, _ -> None
  | NonCollection, _ -> None
  | (SetCollection | MapCollection | ListCollection | SequenceCollection | ArrayCollection), [] -> None

let known_literal_key env value key =
  match value with
  | Dict entries ->
    begin
      match literal_key key with
      | Some key ->
        List.exists (List.filter_map entries ~f:(fun (key, _) -> literal_key key)) ~f:(String.equal key)
      | None -> false
    end
  | Identifier _ ->
    begin
      match literal_key key with
      | Some key -> List.exists (map_keys env (identifier_name value)) ~f:(String.equal key)
      | None -> has_membership env (identifier_name key) (identifier_name value)
    end
  | _ -> false

let validate_membership env left right =
  let right_type = infer env right in
  match membership_type env right_type with
  | Some element ->
    require_compatible (infer env left) element "membership operand has an incompatible type";
    begin
      match collection_kind right_type with
      | SetCollection | MapCollection ->
        require_hashable (infer env left) "membership operand is not hashable"
      | _ -> ()
    end
  | None ->
    require (is_unknown_type right_type) "right operand of membership must be a collection"

let validate_map_lookup env value key =
  match collection_kind (infer env value) with
  | MapCollection ->
    begin
      match map_types (infer env value) with
      | Some (key_type, _) ->
        require_compatible (infer env key) key_type "map lookup key has an incompatible type";
        require_hashable (infer env key) "map lookup key must be hashable";
        require
          (known_literal_key env value key)
          "map lookup requires a key-membership precondition"
      | None -> fail "map lookup requires concrete key and value types"
    end
  | UnknownCollection -> ()
  | _ -> ()

let validate_equality left_type right_type =
  match collection_kind left_type, collection_kind right_type with
  | SetCollection, SetCollection ->
    begin
      match collection_element_type left_type, collection_element_type right_type with
      | Some left, Some right ->
        require_compatible left right "set equality operands have incompatible element types"
      | Some _, None | None, Some _ -> ()
      | None, None -> fail "set equality requires concrete element types"
    end
  | MapCollection, MapCollection ->
    begin
      match map_types left_type, map_types right_type with
      | Some (left_key, left_value), Some (right_key, right_value) ->
        require_compatible left_key right_key "map equality keys have incompatible types";
        require_compatible left_value right_value "map equality values have incompatible types"
      | Some _, None | None, Some _ -> ()
      | _ -> fail "map equality requires concrete key and value types"
    end
  | (SetCollection | MapCollection), _ | _, (SetCollection | MapCollection) ->
    fail "set and map values can only be compared with the same collection kind"
  | _ -> ()

let validate_binary env left operator right =
  let left_type = infer env left in
  let right_type = infer env right in
  let is_set typ = match collection_kind typ with SetCollection -> true | _ -> false in
  match operator with
  | BitOr _ | BitAnd _ ->
    require (is_set left_type && is_set right_type)
      "set algebra requires two sets";
    require_set_elements left_type right_type "set algebra operands have incompatible element types"
  | Minus _ when is_set left_type || is_set right_type ->
    require (is_set left_type && is_set right_type)
      "set difference requires two sets";
    require_set_elements left_type right_type "set difference operands have incompatible element types"
  | In _ | NotIn _ -> validate_membership env left right
  | EqEq _ | NEq _ -> validate_equality left_type right_type
  | _ -> ()

let rec validate_call env callee arguments =
  match callee with
  | Identifier _ ->
    begin
      let name = String.lowercase (identifier_name callee) in
      let name =
        match name with
        | "setf" -> "set"
        | "dictf" -> "dict"
        | name -> name
      in
      match name, arguments with
      | "set", [] -> ()
      | "set", [ iterable ] ->
        begin
          validate_exp env iterable;
          require_set_source (collection_kind (infer env iterable))
            "set() expects a supported typed iterable";
          begin
            match set_source_element_type (infer env iterable) with
            | Some element -> require_hashable element "set() source elements must be hashable"
            | None -> fail "set() expects a concrete source element type"
          end
        end
      | "set", _ -> fail "set() accepts zero or one argument"
      | "dict", [] | "map", [] -> ()
      | "dict", _ | "map", _ -> fail "dict() accepts no arguments in the value-style subset"
      | _, _ -> ()
    end
  | Dot (value, method_name) ->
    let collection = collection_kind (infer env value) in
    let method_name = String.lowercase (Option.value (snd method_name) ~default:"") in
    begin
      match collection, method_name with
      | ListCollection, method_name
        when is_list_mutating_method method_name
             && List.exists env.iterated_lists ~f:(String.equal (identifier_name value)) ->
        fail ("mutating list while iterating it is unsupported: " ^ method_name)
      | SetCollection, ("add" | "remove" | "discard" | "pop" | "clear" | "update"
                        | "intersection_update" | "difference_update" | "symmetric_difference_update")
      | MapCollection, ("pop" | "popitem" | "setdefault" | "update" | "clear") ->
        fail ("mutating collection method is unsupported: " ^ method_name)
      | _ -> ()
    end
  | _ -> ()

and validate_exp env = function
  | Typ _ | Literal _ | Identifier _ -> ()
  | Dot (value, _) -> validate_exp env value
  | BinaryExp (left, operator, right) ->
    validate_exp env left;
    validate_exp env right;
    validate_binary env left operator right
  | CompareChain (first, comparisons) ->
    validate_exp env first;
    let rec validate_chain previous = function
      | [] -> ()
      | (operator, operand) :: rest ->
        validate_exp env operand;
        validate_binary env previous operator operand;
        validate_chain operand rest
    in
    validate_chain first comparisons
  | UnaryExp (_, value) -> validate_exp env value
  | Call (callee, arguments) ->
    validate_exp env callee;
    List.iter arguments ~f:(validate_exp env);
    validate_call env callee arguments
  | Lst elements | Array elements ->
    List.iter elements ~f:(validate_exp env);
    begin
      match elements with
      | [] -> ()
      | first :: rest ->
        let first_type = infer env first in
        List.iter rest ~f:(fun element -> require_compatible first_type (infer env element) "collection elements have incompatible types")
    end
  | Set elements ->
    List.iter elements ~f:(validate_exp env);
    begin
      match elements with
      | [] -> ()
      | first :: rest ->
        let first_type = infer env first in
        require_hashable first_type "set elements must be hashable";
        List.iter rest ~f:(fun element ->
          require_compatible first_type (infer env element) "collection elements have incompatible types";
          require_hashable (infer env element) "set elements must be hashable")
    end
  | Dict entries ->
    List.iter entries ~f:(fun (key, value) -> validate_exp env key; validate_exp env value);
    begin
      match entries with
      | [] -> ()
      | (first_key, first_value) :: rest ->
        let key_type = infer env first_key in
        let value_type = infer env first_value in
        require_hashable key_type "dictionary keys must be hashable";
        List.iter rest ~f:(fun (key, value) ->
          require_compatible key_type (infer env key) "dictionary keys have incompatible types";
          require_hashable (infer env key) "dictionary keys must be hashable";
          require_compatible value_type (infer env value) "dictionary values have incompatible types")
    end
  | Tuple elements -> List.iter elements ~f:(validate_exp env)
  | SingletonTuple (_, value) -> validate_exp env value
  | Subscript (value, selector) ->
    validate_exp env value;
    validate_exp env selector;
    begin
      match selector, collection_kind (infer env value) with
      | Index key, MapCollection -> validate_map_lookup env value key
      | Index key, (ListCollection | SequenceCollection | ArrayCollection | TupleCollection) ->
        ignore (infer env key)
      | Index _, UnknownCollection -> ()
      | Index _, _ -> fail "value is not indexable"
      | Slice _, (ListCollection | SequenceCollection | ArrayCollection | TupleCollection | UnknownCollection) -> ()
      | Slice _, _ -> fail "value does not support slicing"
      | _, _ -> fail "subscript selector must be an index or slice"
    end
  | Index value -> validate_exp env value
  | Slice (lower, upper) ->
    Option.iter lower ~f:(validate_exp env);
    Option.iter upper ~f:(validate_exp env)
  | Forall (identifiers, body) | Exists (identifiers, body) ->
    let scoped = enter_scope env ComprehensionScope in
    let scoped = bind_many scoped (List.map identifiers ~f:(fun identifier -> identifier_name (Identifier identifier), TIdent identifier)) in
    validate_exp scoped body
  | Len (_, value) ->
    validate_exp env value;
    require_collection (collection_kind (infer env value)) "len() expects a known collection"
  | Max (_, value) -> validate_exp env value
  | Old (_, value) | Fresh (_, value) -> validate_exp env value
  | Lambda (identifiers, body) ->
    let scoped = enter_scope env (FunctionScope "lambda") in
    let scoped = bind_many scoped (List.map identifiers ~f:(fun identifier -> identifier_name (Identifier identifier), TIdent identifier)) in
    validate_exp scoped body
  | IfElseExp (when_true, condition, when_false) ->
    validate_exp env condition;
    validate_exp env when_true;
    validate_exp env when_false

and validate_spec env = function
  | Pre value -> validate_exp env value; assume_membership env value
  | Post value | Invariant value | Decreases value | Reads value | Modifies value ->
    validate_exp env value;
    env

and validate_specs env specifications =
  List.fold specifications ~init:env ~f:(fun env specification -> validate_spec env specification)

and validate_loop_specs env specifications =
  List.fold specifications ~init:env ~f:(fun env specification ->
    match specification with
    | Invariant value | Decreases value ->
      validate_exp env value;
      env
    | Pre _ | Post _ | Reads _ | Modifies _ ->
      fail "loop specifications support only invariant and decreases")

and validate_target env = function
  | Identifier _ -> ()
  | Dot (value, _) -> validate_exp env value
  | Subscript (value, Index key) ->
    validate_exp env value;
    validate_exp env key;
    begin
      require
        (match value with
         | Subscript _ -> false
         | _ -> true)
        "nested map updates are unsupported";
      match collection_kind (infer env value) with
      | MapCollection ->
        require (match value with Identifier _ -> true | _ -> false)
          "map updates require a local map variable";
        require
          (not (List.exists env.map_aliases ~f:(String.equal (identifier_name value))))
          "map updates through aliases are unsupported";
        begin
          match map_types (infer env value) with
          | Some (key_type, _) ->
            require_compatible (infer env key) key_type "map update key has an incompatible type";
            require_hashable (infer env key) "map update key must be hashable"
          | None -> fail "map update requires concrete key and value types"
        end
      | ListCollection -> fail "indexed assignment into List is unsupported"
      | _ -> ()
    end
  | Subscript (value, selector) -> validate_exp env (Subscript (value, selector))
  | Tuple targets -> List.iter targets ~f:(validate_target env)
  | _ -> fail "assignment target is not supported"

and validate_assignment env annotation_opt targets values =
  Option.iter annotation_opt ~f:(validate_exp env);
  List.iter targets ~f:(validate_target env);
  List.iter values ~f:(validate_exp env);
  let declared = Option.map annotation_opt ~f:annotation in
  let bindings = List.map2_exn targets values ~f:(fun target value -> target, value, infer env value) in
  let env =
    List.fold bindings ~init:env ~f:(fun env (target, value, value_type) ->
      match target, value, value_type with
      | Identifier _, value, value_type ->
        let name = identifier_name target in
        let value_type = Option.value declared ~default:value_type in
        bind_value env name value_type value
      | Subscript (Identifier map, Index key), _, value_type ->
        begin
          match collection_kind (infer env (Identifier map)) with
          | MapCollection ->
            let expected_value_type =
              Option.value_map (map_types (infer env (Identifier map)))
                ~default:(TIdent def_seg) ~f:snd
            in
            require_compatible value_type expected_value_type "map update value has an incompatible type";
            add_map_key env (identifier_name (Identifier map)) key
          | _ -> env
        end
      | _ -> env)
  in
  env

and validate_statements env statements =
  List.fold statements ~init:env ~f:(fun env statement ->
    match statement with
    | Assign (annotation_opt, targets, values) -> validate_assignment env annotation_opt targets values
    | Function (specifications, name, _parameters, return_type, body) ->
      let signature = Option.value_exn (lookup_function env (identifier_name (Identifier name))) in
      let function_env = enter_scope env (FunctionScope signature.name) in
      let function_env = bind_many function_env signature.parameters in
      let function_env = bind function_env "return" (annotation return_type) in
      let function_env = validate_specs function_env specifications in
      ignore (validate_statements function_env body);
      env
    | IfElse (condition, first, alternatives, last) ->
      validate_exp env condition;
      let env = validate_statements (assume_membership env condition) first in
      let env =
        List.fold alternatives ~init:env ~f:(fun env (condition, body) ->
          validate_exp env condition;
          validate_statements (assume_membership env condition) body)
      in
      validate_statements env last
    | While (specifications, condition, body) ->
      let env = validate_loop_specs env specifications in
      validate_exp env condition;
      ignore (validate_statements env body);
      env
    | For (specifications, identifiers, iterable, body) ->
      let env = validate_loop_specs env specifications in
      validate_exp env iterable;
      begin
        match collection_kind (infer env iterable) with
        | SetCollection ->
          require (Option.is_some (collection_element_type (infer env iterable)))
            "set iteration requires a concrete element type";
          require (List.length identifiers = 1) "set/map iteration requires one loop target"
        | MapCollection ->
          require (Option.is_some (map_types (infer env iterable)))
            "map iteration requires concrete key and value types";
          require (List.length identifiers = 1) "set/map iteration requires one loop target"
        | ListCollection | SequenceCollection ->
          require (List.length identifiers = 1)
            "list/sequence iteration requires one loop target"
        | UnknownCollection -> raise (SemanticError "for loop iterable requires a known type")
        | ArrayCollection | TupleCollection | StringCollection | NonCollection ->
          raise (SemanticError "for loop iterable is not supported")
      end;
      let element =
        match collection_arguments (infer env iterable) with
        | element :: _ -> element
        | _ -> TIdent def_seg
      in
      let loop_env = enter_scope env ComprehensionScope in
      let identifier = List.hd_exn identifiers in
      let loop_env =
        match collection_kind (infer env iterable), iterable with
        | ListCollection, Identifier source ->
          { loop_env with
            iterated_lists = list_aliases_for env (identifier_name (Identifier source))
                             @ loop_env.iterated_lists }
        | MapCollection, Identifier source ->
          add_membership loop_env (identifier_name (Identifier identifier))
            (identifier_name (Identifier source))
        | _ -> loop_env
      in
      let loop_env = bind loop_env (identifier_name (Identifier identifier)) element in
      ignore (validate_statements loop_env body);
      env
    | Return value | Assert value | Exp value -> validate_exp env value; env
    | Break | Continue | Pass -> env)

let analyze (Program statements) =
  match normalize_program (Program statements) with
  | Program statements ->
    let env = collect_functions empty statements |> fun env -> classify_functions env statements in
    validate_statements env statements
