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
  }

let empty = { scopes = [ { kind = Global; bindings = [] } ]; functions = []; classes = [] }

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
    { env with scopes = { scope with bindings } :: rest }

let bind_many env bindings =
  List.fold bindings ~init:env ~f:(fun env (name, typ) -> bind env name typ)

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
    end
  | CompareChain _ -> TBool def_seg
  | SingletonTuple (_, value) -> infer env value
  | Call (callee, arguments) ->
    begin
      match callee with
      | Identifier segment ->
        begin
          match Option.value (snd segment) ~default:"" with
          | "len" -> TInt def_seg
          | "list" ->
            let element = match arguments with
              | [ Lst elements ] -> List.find_map elements ~f:(fun element -> Some (infer env element))
              | _ -> None
            in
            generic "list" (Option.to_list element)
          | "set" -> generic "set" []
          | "dict" | "map" -> generic "map" []
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

let rec analyze_statements env statements =
  List.fold statements ~init:env ~f:(fun env statement ->
    match statement with
    | Assign (annotation_opt, targets, values) ->
      let values = List.map values ~f:(infer env) in
      let declared =
        match annotation_opt with
        | Some value -> annotation value
        | None -> TIdent def_seg
      in
      let bindings = List.map2_exn targets values ~f:(fun target value ->
        let value = if String.equal (type_name declared) "" then value else declared in
        match target with
        | Identifier identifier -> Option.value (snd identifier) ~default:"", value
        | _ -> "", value)
      in
      bind_many env (List.filter bindings ~f:(fun (name, _) -> not (String.is_empty name)))
    | Function (_, name, _parameters, return_type, body) ->
      let signature = Option.value_exn (lookup_function env (Option.value (snd name) ~default:"")) in
      let function_env = enter_scope env (FunctionScope signature.name) in
      let function_env = bind_many function_env signature.parameters in
      let function_env = bind function_env "return" (annotation return_type) in
      ignore (analyze_statements function_env body);
      env
    | IfElse (condition, first, alternatives, last) ->
      ignore (infer env condition);
      let env = analyze_statements env first in
      let env = List.fold alternatives ~init:env ~f:(fun env (condition, body) -> ignore (infer env condition); analyze_statements env body) in
      analyze_statements env last
    | While (specifications, condition, body) ->
      List.iter specifications ~f:(fun specification -> ignore (infer_spec env specification));
      ignore (infer env condition);
      analyze_statements env body
    | For (specifications, identifiers, iterable, body) ->
      List.iter specifications ~f:(fun specification -> ignore (infer_spec env specification));
      let element = match generic_arguments (infer env iterable) with | element :: _ -> element | [] -> TIdent def_seg in
      let loop_env = enter_scope env ComprehensionScope in
      let loop_env = bind_many loop_env (List.map identifiers ~f:(fun identifier -> Option.value (snd identifier) ~default:"", element)) in
      ignore (analyze_statements loop_env body);
      env
    | Assert value | Exp value | Return value -> ignore (infer env value); env
    | Break | Continue | Pass -> env)

and infer_spec env = function
  | Pre value | Post value | Invariant value | Decreases value | Reads value | Modifies value -> infer env value

let analyze (Program statements) =
  match normalize_program (Program statements) with
  | Program statements ->
    let env = collect_functions empty statements in
    analyze_statements env statements
