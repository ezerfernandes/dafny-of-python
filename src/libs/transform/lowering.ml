open Base

module Py = Pyparse.Astpy
module D = Astdfy
module S = Pyparse.Sourcemap
module Sem = Semantic

type evaluation = Eager | Scoped

type context =
  { environment : Sem.environment
  ; evaluation : evaluation
  ; expected_type : Py.typ option
  ; return_type : Py.typ option
  ; loop_depth : int
  ; iterated_lists : string list
  ; iterated_maps : string list
  ; check_map_iteration_order : bool
  }

type lowered =
  { prelude : D.dStmt list
  ; result : D.dExpr
  ; resolved_type : Py.typ
  ; control_flow : bool
  ; effectful : bool
  }

type lvalue =
  | Local of S.segment
  | Field of D.dExpr * S.segment
  | Index of D.dExpr * D.dExpr
  | TupleTarget of lvalue list

type lowered_lvalue =
  { prelude : D.dStmt list
  ; target : D.dLvalue
  }

type slice_kind = BothBounds | LowerBound | UpperBound | NoBounds
type selector_kind = IndexSelector of Py.exp | SliceSelector of slice_kind * D.dExpr list

exception LoweringError of string

let fail message = raise (LoweringError message)

let temp_number = ref 0
let reserved_names = ref []

let reset () =
  temp_number := 0;
  reserved_names := []

let reserve_name name =
  if not (String.is_empty name) && not (List.mem !reserved_names name ~equal:String.equal) then
    reserved_names := name :: !reserved_names

let reserve_segment segment = Option.iter (snd segment) ~f:reserve_name

[@@@coverage off]
let rec reserve_type = function
  | Py.TIdent segment | Py.TInt segment | Py.TFloat segment | Py.TBool segment
  | Py.TStr segment | Py.TNone segment | Py.TObj segment -> reserve_segment segment
  | Py.TLst (segment, element) | Py.TSet (segment, element) | Py.TType (segment, element) ->
    reserve_segment segment;
    Option.iter element ~f:reserve_type
  | Py.TDict (segment, key, value) ->
    reserve_segment segment;
    Option.iter key ~f:reserve_type;
    Option.iter value ~f:reserve_type
  | Py.TTuple (segment, elements) ->
    reserve_segment segment;
    Option.iter elements ~f:(List.iter ~f:reserve_type)
  | Py.TCallable (segment, parameters, result) ->
    reserve_segment segment;
    List.iter parameters ~f:reserve_type;
    reserve_type result
  | Py.TGeneric (segment, arguments) ->
    reserve_segment segment;
    List.iter arguments ~f:reserve_type

and reserve_expression = function
  | Py.Typ typ -> reserve_type typ
  | Py.Literal _ -> ()
  | Py.Identifier identifier -> reserve_segment identifier
  | Py.Dot (value, identifier) ->
    reserve_expression value;
    reserve_segment identifier
  | Py.BinaryExp (left, operator, right) ->
    reserve_expression left;
    ignore operator;
    reserve_expression right
  | Py.CompareChain (first, comparisons) ->
    reserve_expression first;
    List.iter comparisons ~f:(fun (operator, operand) ->
      ignore operator;
      reserve_expression operand)
  | Py.UnaryExp (operator, value) ->
    ignore operator;
    reserve_expression value
  | Py.Call (callee, arguments) ->
    reserve_expression callee;
    List.iter arguments ~f:reserve_expression
  | Py.Lst elements | Py.Array elements | Py.Set elements | Py.Tuple elements ->
    List.iter elements ~f:reserve_expression
  | Py.ListComprehension (result, clauses) | Py.SetComprehension (result, clauses) ->
    reserve_expression result;
    List.iter clauses ~f:reserve_clause
  | Py.DictComprehension (key, value, clauses) ->
    reserve_expression key;
    reserve_expression value;
    List.iter clauses ~f:reserve_clause
  | Py.Dict entries ->
    List.iter entries ~f:(fun (key, value) -> reserve_expression key; reserve_expression value)
  | Py.SingletonTuple (comma, value) ->
    reserve_segment comma;
    reserve_expression value
  | Py.Subscript (value, selector) ->
    reserve_expression value;
    reserve_expression selector
  | Py.Index value -> reserve_expression value
  | Py.Slice (lower, upper) ->
    Option.iter lower ~f:reserve_expression;
    Option.iter upper ~f:reserve_expression
  | Py.Forall (identifiers, body) | Py.Exists (identifiers, body) | Py.Lambda (identifiers, body) ->
    List.iter identifiers ~f:reserve_segment;
    reserve_expression body
  | Py.Len (segment, value) | Py.Max (segment, value) | Py.Old (segment, value)
  | Py.Fresh (segment, value) ->
    reserve_segment segment;
    reserve_expression value
  | Py.IfElseExp (when_true, condition, when_false) ->
    reserve_expression when_true;
    reserve_expression condition;
    reserve_expression when_false

and reserve_clause = function
  | Py.ComprehensionFor (targets, iterable) ->
    List.iter targets ~f:reserve_segment;
    reserve_expression iterable
  | Py.ComprehensionIf condition -> reserve_expression condition

and reserve_specification = function
  | Py.Pre value | Py.Post value | Py.Invariant value | Py.Decreases value
  | Py.Reads value | Py.Modifies value -> reserve_expression value

and reserve_statement = function
  | Py.IfElse (condition, first, alternatives, last) ->
    reserve_expression condition;
    List.iter first ~f:reserve_statement;
    List.iter alternatives ~f:(fun (condition, body) ->
      reserve_expression condition;
      List.iter body ~f:reserve_statement);
    List.iter last ~f:reserve_statement
  | Py.For (specifications, identifiers, iterable, body) ->
    List.iter specifications ~f:reserve_specification;
    List.iter identifiers ~f:reserve_segment;
    reserve_expression iterable;
    List.iter body ~f:reserve_statement
  | Py.While (specifications, condition, body) ->
    List.iter specifications ~f:reserve_specification;
    reserve_expression condition;
    List.iter body ~f:reserve_statement
  | Py.Assign (annotation, targets, values) ->
    Option.iter annotation ~f:reserve_expression;
    List.iter targets ~f:reserve_expression;
    List.iter values ~f:reserve_expression
  | Py.Function (specifications, name, parameters, return_type, body) ->
    List.iter specifications ~f:reserve_specification;
    reserve_segment name;
    List.iter parameters ~f:(fun (identifier, annotation) ->
      reserve_segment identifier;
      reserve_expression annotation);
    reserve_expression return_type;
    List.iter body ~f:reserve_statement
  | Py.Return value | Py.Assert value | Py.Exp value -> reserve_expression value
  | Py.Break | Py.Continue | Py.Pass -> ()
[@@@coverage on]

let reserve_environment (environment : Sem.environment) =
  List.iter environment.scopes ~f:(fun scope ->
    List.iter scope.bindings ~f:(fun (name, typ) ->
      reserve_name name;
      reserve_type typ));
  List.iter environment.functions ~f:(fun signature -> reserve_name signature.name)

let reserve_statements statements = List.iter statements ~f:reserve_statement

let fresh_temp () =
  let rec next () =
    Int.incr temp_number;
    let name = "lowered_" ^ Int.to_string !temp_number in
    if List.mem !reserved_names name ~equal:String.equal then next ()
    else (
      reserve_name name;
      (S.def_pos, Some name))
  in
  next ()

let context environment =
  { environment
  ; evaluation = Eager
  ; expected_type = None
  ; return_type = None
  ; loop_depth = 0
  ; iterated_lists = []
  ; iterated_maps = []
  ; check_map_iteration_order = true
  }

let scoped context = { context with evaluation = Scoped }

let is_eager context =
  match context.evaluation with
  | Eager -> true
  | Scoped -> false

let with_expected_type context expected_type = { context with expected_type = Some expected_type }

let with_return_type context return_type = { context with return_type = Some return_type }

let generic_name typ =
  match Sem.normalize_type typ with
  | Py.TGeneric (segment, _) ->
    Option.value (snd segment) ~default:"" |> String.lowercase
  | _ -> ""

let generic_arguments typ =
  match Sem.normalize_type typ with
  | Py.TGeneric (_, arguments) -> arguments
  | _ -> []

let rec type_dfy = function
  | Py.TIdent segment -> D.DIdentTyp (segment, [])
  | Py.TInt segment -> D.DInt segment
  | Py.TFloat segment -> D.DReal segment
  | Py.TBool segment -> D.DBool segment
  | Py.TStr segment -> D.DString segment
  | Py.TNone _ -> D.DVoid
  | Py.TObj segment -> D.DObj segment
  | Py.TLst (segment, Some element) ->
    D.DIdentTyp ((fst segment, Some "List"), [ type_dfy element ])
  | Py.TLst (_, None) -> fail "Please specify the exact sequence type"
  | Py.TDict (segment, Some key, Some value) -> D.DMap (segment, type_dfy key, type_dfy value)
  | Py.TDict (_, _, _) -> fail "Please specify the exact map type"
  | Py.TSet (segment, Some element) -> D.DSet (segment, type_dfy element)
  | Py.TSet (_, None) -> fail "Please specify the exact set type"
  | Py.TTuple (segment, Some elements) -> D.DTuple (segment, List.map elements ~f:type_dfy)
  | Py.TTuple (segment, None) -> D.DTuple (segment, [])
  | Py.TCallable (segment, parameters, result) ->
    D.DFunTyp (segment, List.map parameters ~f:type_dfy, type_dfy result)
  | Py.TType (_, Some element) -> type_dfy element
  | Py.TType (_, None) -> fail "Please specify the exact type"
  | Py.TGeneric (segment, arguments) ->
    let name = Option.value (snd segment) ~default:"" |> String.lowercase in
    begin
      match name, arguments with
      | "list", [ element ] -> D.DIdentTyp ((fst segment, Some "List"), [ type_dfy element ])
      | "seq", [ element ] -> D.DSeq (segment, type_dfy element)
      | "set", [ element ] -> D.DSet (segment, type_dfy element)
      | "map", [ key; value ] -> D.DMap (segment, type_dfy key, type_dfy value)
      | "array", [ element ] -> D.DArray (segment, type_dfy element)
      | "tuple", elements -> D.DTuple (segment, List.map elements ~f:type_dfy)
      | _ -> D.DIdentTyp (segment, List.map arguments ~f:type_dfy)
    end

let annotation_type = function
  | Py.Typ typ -> typ
  | Py.Identifier identifier -> Py.TIdent identifier
  | _ -> fail "Invalid type of assignment"

let literal_dfy = function
  | Py.TrueLit -> D.DTrue
  | Py.FalseLit -> D.DFalse
  | Py.IntLit value -> D.DIntLit value
  | Py.FloatLit value -> D.DRealLit value
  | Py.StringLit value -> D.DStringLit value
  | Py.NoneLit -> D.DNull

let unary_operator = function
  | Py.Not segment -> D.DNot segment
  | Py.UMinus segment -> D.DMinus segment

let binary_operator = function
  | Py.NotIn segment -> D.DNotIn segment
  | Py.In segment -> D.DIn segment
  | Py.Plus segment -> D.DPlus segment
  | Py.Minus segment -> D.DMinus segment
  | Py.Times segment -> D.DTimes segment
  | Py.Divide segment -> D.DDivide segment
  | Py.Mod segment -> D.DMod segment
  | Py.NEq segment -> D.DNEq segment
  | Py.EqEq segment -> D.DEq segment
  | Py.Lt segment -> D.DLt segment
  | Py.LEq segment -> D.DLEq segment
  | Py.Gt segment -> D.DGt segment
  | Py.GEq segment -> D.DGEq segment
  | Py.And segment -> D.DAnd segment
  | Py.Or segment -> D.DOr segment
  | Py.BiImpl segment -> D.DBiImpl segment
  | Py.Implies segment -> D.DImplies segment
  | Py.Explies segment -> D.DExplies segment
  | Py.BitOr segment -> D.DSetUnion segment
  | Py.BitAnd segment -> D.DSetIntersection segment

let collection_binary_operator environment left operator right =
  let is_set expression =
    match Sem.collection_kind (Sem.infer environment expression) with
    | Sem.SetCollection -> true
    | _ -> false
  in
  match operator with
  | Py.Minus segment when is_set left && is_set right -> D.DSetDifference segment
  | Py.BitOr segment -> D.DSetUnion segment
  | Py.BitAnd segment -> D.DSetIntersection segment
  | _ -> binary_operator operator

let binary_expression environment left operator right left_result right_result =
  let list_contents result = D.DDot (result, (S.def_pos, Some "lst")) in
  let lists_are_equal =
    match Sem.collection_kind (Sem.infer environment left),
          Sem.collection_kind (Sem.infer environment right) with
    | Sem.ListCollection, Sem.ListCollection -> true
    | _ -> false
  in
  match operator, lists_are_equal, Sem.collection_kind (Sem.infer environment right) with
  | Py.EqEq segment, true, _ ->
    D.DBinary (list_contents left_result, D.DEq segment, list_contents right_result)
  | Py.NEq segment, true, _ ->
    D.DUnary
      (D.DNot segment,
       D.DBinary (list_contents left_result, D.DEq segment, list_contents right_result))
  | Py.In _, _, Sem.ListCollection ->
    D.DCallExpr
      (D.DDot (right_result, (S.def_pos, Some "contains")), [ left_result ])
  | Py.NotIn segment, _, Sem.ListCollection ->
    D.DUnary
      (D.DNot segment,
       D.DCallExpr
         (D.DDot (right_result, (S.def_pos, Some "contains")), [ left_result ]))
  | _ ->
    D.DBinary
      (left_result, collection_binary_operator environment left operator right, right_result)

let empty_list_type expected_type =
  match expected_type with
  | None -> fail "empty list literals require a concrete list type"
  | Some expected_type ->
    let expected_type = Sem.normalize_type expected_type in
    begin
      match Sem.collection_kind expected_type, Sem.collection_element_type expected_type with
      | Sem.ListCollection, Some _ -> expected_type
      | Sem.ListCollection, None -> fail "empty list literals require a concrete element type"
      | _ -> fail "empty list literals require a list type"
    end

let reject_list_assignment () = fail "indexed assignment into List is unsupported"

let materialize context (lowered : lowered) =
  match context.evaluation with
  | Scoped -> lowered
  | Eager ->
    let identifier = fresh_temp () in
    { lowered with
      prelude = lowered.prelude @ [ D.DAssignLvalue (None, [ D.Local identifier ], [ lowered.result ]) ]
    ; result = D.DIdentifier identifier
    }

let result_needs_capture = function
  | D.DIdentifier _ | D.DIntLit _ | D.DRealLit _ | D.DTrue | D.DFalse
  | D.DStringLit _ | D.DNull -> false
  | _ -> true

let join_preludes (lowered : lowered list) =
  List.concat_map lowered ~f:(fun value -> value.prelude)

let results (lowered : lowered list) = List.map lowered ~f:(fun value -> value.result)

let reject_scoped_comprehension () =
  "comprehensions are unsupported in scoped expressions"

let reject_non_comprehension () = "internal error: expected a comprehension"

[@@@coverage off]
let rec rename_comprehension_expression substitutions = function
  | Py.Typ _ | Py.Literal _ as expression -> expression
  | Py.Identifier identifier ->
    let identifier =
      match snd identifier with
      | Some name -> Option.value (List.Assoc.find substitutions name ~equal:String.equal) ~default:identifier
      | None -> identifier
    in
    Py.Identifier identifier
  | Py.Dot (value, identifier) ->
    Py.Dot (rename_comprehension_expression substitutions value, identifier)
  | Py.BinaryExp (left, operator, right) ->
    Py.BinaryExp
      ( rename_comprehension_expression substitutions left
      , operator
      , rename_comprehension_expression substitutions right )
  | Py.CompareChain (first, comparisons) ->
    Py.CompareChain
      ( rename_comprehension_expression substitutions first
      , List.map comparisons ~f:(fun (operator, operand) ->
          operator, rename_comprehension_expression substitutions operand) )
  | Py.UnaryExp (operator, value) ->
    Py.UnaryExp (operator, rename_comprehension_expression substitutions value)
  | Py.Call (callee, arguments) ->
    Py.Call
      ( rename_comprehension_expression substitutions callee
      , List.map arguments ~f:(rename_comprehension_expression substitutions) )
  | Py.Lst elements ->
    Py.Lst (List.map elements ~f:(rename_comprehension_expression substitutions))
  | Py.Array elements ->
    Py.Array (List.map elements ~f:(rename_comprehension_expression substitutions))
  | Py.Set elements ->
    Py.Set (List.map elements ~f:(rename_comprehension_expression substitutions))
  | Py.Dict entries ->
    Py.Dict
      (List.map entries ~f:(fun (key, value) ->
         rename_comprehension_expression substitutions key
         , rename_comprehension_expression substitutions value))
  | Py.ListComprehension (result, clauses) ->
    let clauses, substitutions = rename_comprehension_clauses substitutions clauses in
    Py.ListComprehension
      ( rename_comprehension_expression substitutions result
      , clauses )
  | Py.SetComprehension (result, clauses) ->
    let clauses, substitutions = rename_comprehension_clauses substitutions clauses in
    Py.SetComprehension
      ( rename_comprehension_expression substitutions result
      , clauses )
  | Py.DictComprehension (key, value, clauses) ->
    let clauses, substitutions = rename_comprehension_clauses substitutions clauses in
    Py.DictComprehension
      ( rename_comprehension_expression substitutions key
      , rename_comprehension_expression substitutions value
      , clauses )
  | Py.Tuple elements ->
    Py.Tuple (List.map elements ~f:(rename_comprehension_expression substitutions))
  | Py.SingletonTuple (comma, value) ->
    Py.SingletonTuple (comma, rename_comprehension_expression substitutions value)
  | Py.Subscript (value, selector) ->
    Py.Subscript
      ( rename_comprehension_expression substitutions value
      , rename_comprehension_expression substitutions selector )
  | Py.Index value -> Py.Index (rename_comprehension_expression substitutions value)
  | Py.Slice (lower, upper) ->
    Py.Slice
      ( Option.map lower ~f:(rename_comprehension_expression substitutions)
      , Option.map upper ~f:(rename_comprehension_expression substitutions) )
  | Py.Forall (identifiers, body) ->
    Py.Forall (identifiers, rename_comprehension_expression substitutions body)
  | Py.Exists (identifiers, body) ->
    Py.Exists (identifiers, rename_comprehension_expression substitutions body)
  | Py.Len (segment, value) ->
    Py.Len (segment, rename_comprehension_expression substitutions value)
  | Py.Max (segment, value) ->
    Py.Max (segment, rename_comprehension_expression substitutions value)
  | Py.Old (segment, value) ->
    Py.Old (segment, rename_comprehension_expression substitutions value)
  | Py.Fresh (segment, value) ->
    Py.Fresh (segment, rename_comprehension_expression substitutions value)
  | Py.Lambda (identifiers, body) ->
    Py.Lambda (identifiers, rename_comprehension_expression substitutions body)
  | Py.IfElseExp (when_true, condition, when_false) ->
    Py.IfElseExp
      ( rename_comprehension_expression substitutions when_true
      , rename_comprehension_expression substitutions condition
      , rename_comprehension_expression substitutions when_false )

and rename_comprehension_clauses substitutions clauses =
  let rec loop substitutions = function
    | [] -> [], substitutions
    | Py.ComprehensionFor (targets, iterable) :: rest ->
      let iterable = rename_comprehension_expression substitutions iterable in
      let targets, substitutions =
        List.fold targets ~init:([], substitutions) ~f:(fun (targets, substitutions) target ->
          let renamed = fresh_temp () in
          let name = Option.value (snd target) ~default:"" in
          renamed :: targets, (name, renamed) :: substitutions)
      in
      let rest, substitutions = loop substitutions rest in
      Py.ComprehensionFor (List.rev targets, iterable) :: rest, substitutions
    | Py.ComprehensionIf condition :: rest ->
      let rest, substitutions = loop substitutions rest in
      Py.ComprehensionIf (rename_comprehension_expression substitutions condition) :: rest, substitutions
  in
  loop substitutions clauses
[@@@coverage on]

let rec preserve_before_prelude context (values : lowered list) : lowered list =
  match values with
  | [] -> []
  | value :: rest ->
    let rest = preserve_before_prelude context rest in
    let value =
      if is_eager context
         && result_needs_capture value.result
         && List.exists rest ~f:(fun value -> not (List.is_empty value.prelude))
      then
        materialize context value
      else value
    in
    value :: rest

let rec lower_many context expressions =
  let lowered = List.map expressions ~f:(lower context) in
  preserve_before_prelude context lowered

and lower_collection context constructor expressions resolved_type =
  let lowered = lower_many context expressions in
  { prelude = join_preludes lowered
  ; result = constructor (results lowered)
  ; resolved_type
  ; control_flow = List.exists lowered ~f:(fun value -> value.control_flow)
  ; effectful = List.exists lowered ~f:(fun value -> value.effectful)
  }

and lower_map context entries =
  let lowered_values =
    lower_many context (List.concat_map entries ~f:(fun (key, value) -> [ key; value ]))
  in
  let pair_values values =
    List.mapi entries ~f:(fun index _entry ->
      ( List.nth_exn values (index * 2)
      , List.nth_exn values (index * 2 + 1) ))
  in
  let lowered = pair_values lowered_values in
  let result =
    List.fold lowered ~init:(D.DMapExpr []) ~f:(fun result (key, value) ->
      D.DMapUpdate (result, key.result, value.result))
  in
  { prelude = List.concat_map lowered ~f:(fun (key, value) -> key.prelude @ value.prelude)
  ; result
  ; resolved_type = Sem.infer context.environment (Py.Dict entries)
  ; control_flow = List.exists lowered ~f:(fun (key, value) -> key.control_flow || value.control_flow)
  ; effectful = List.exists lowered ~f:(fun (key, value) -> key.effectful || value.effectful)
  }

and lower_list context elements =
  let resolved_type =
    match elements, context.expected_type with
    | [], expected_type -> empty_list_type expected_type
    | _, _ -> Sem.infer context.environment (Py.Lst elements)
  in
  let element_context =
    Option.value_map (Sem.collection_element_type resolved_type)
      ~default:context
      ~f:(with_expected_type context)
  in
  let lowered = lower_many element_context elements in
  match context.evaluation with
  | Scoped -> fail "list literals cannot be constructed inside a scoped expression"
  | Eager ->
    let identifier = fresh_temp () in
    { prelude =
        join_preludes lowered
        @ [ D.DAssignLvalue
              (None, [ D.Local identifier ]
               , [ D.DNew (type_dfy resolved_type, [ D.DSeqExpr (results lowered) ]) ]) ]
    ; result = D.DIdentifier identifier
    ; resolved_type
    ; control_flow = List.exists lowered ~f:(fun value -> value.control_flow)
    ; effectful = List.exists lowered ~f:(fun value -> value.effectful)
    }

and lower_set_constructor context callee arguments =
  let resolved_type = Sem.infer context.environment (Py.Call (callee, arguments)) in
  match arguments with
  | [] ->
    { prelude = []; result = D.DSetExpr []; resolved_type; control_flow = false; effectful = false }
  | [ iterable ] ->
    let lowered = lower context iterable in
    begin
      match Sem.collection_kind lowered.resolved_type with
      | Sem.SetCollection -> lowered
      | Sem.MapCollection ->
        { lowered with
          result = D.DMapKeys lowered.result
        ; resolved_type = resolved_type
        }
      | Sem.ListCollection ->
        { lowered with
          result = D.DCallExpr (D.DIdentifier (S.def_pos, Some "setFromSeq"),
                                [ D.DDot (lowered.result, (S.def_pos, Some "lst")) ])
        ; resolved_type
        }
      | Sem.SequenceCollection ->
        { lowered with
          result = D.DCallExpr (D.DIdentifier (S.def_pos, Some "setFromSeq"), [ lowered.result ])
        ; resolved_type
        }
      | _ -> fail "set() expects a set, list, sequence, or map"
    end
  | _ -> fail "set() accepts zero or one argument"

and lower_dict_constructor context callee arguments =
  match arguments with
  | [] ->
    { prelude = []; result = D.DMapExpr []; resolved_type = Sem.infer context.environment (Py.Call (callee, arguments)); control_flow = false; effectful = false }
  | _ -> fail "dict() accepts no arguments in the value-style subset"

and lower_call context callee arguments =
  match callee with
  | Py.Identifier identifier
    when List.mem [ "set"; "setf" ] (Option.value (snd identifier) ~default:"" |> String.lowercase)
         ~equal:String.equal ->
    lower_set_constructor context (Py.Identifier identifier) arguments
  | Py.Identifier identifier
    when List.mem [ "dict"; "dictf"; "map" ] (Option.value (snd identifier) ~default:"" |> String.lowercase)
         ~equal:String.equal ->
    lower_dict_constructor context (Py.Identifier identifier) arguments
  | _ -> lower_regular_call context callee arguments

and reject_iterated_list_mutation context callee =
  match callee with
  | Py.Dot (Py.Identifier identifier, method_name) ->
    let name = Option.value (snd identifier) ~default:"" in
    let method_name = Option.value (snd method_name) ~default:"" in
    begin
      match Sem.collection_kind (Sem.infer context.environment (Py.Identifier identifier)) with
      | Sem.ListCollection
        when Sem.is_list_mutating_method method_name
             && List.exists context.iterated_lists ~f:(fun iterated ->
                  Sem.may_alias_list context.environment name iterated) ->
        fail ("mutating list while iterating it is unsupported: " ^ String.lowercase method_name)
      | _ -> ()
    end
  | _ -> ()

and lower_regular_call context callee arguments =
  reject_iterated_list_mutation context callee;
  let lowered_callee = lower context callee in
  let parameter_types =
    match Sem.normalize_type (Sem.infer context.environment callee) with
    | Py.TCallable (_, parameters, _) -> parameters
    | _ -> []
  in
  let rec lower_arguments parameter_types = function
    | [] -> []
    | argument :: rest ->
      let argument_context =
        match parameter_types with
        | parameter_type :: _ -> with_expected_type context parameter_type
        | [] -> context
      in
      lower argument_context argument ::
      lower_arguments
        (match parameter_types with
         | _ :: rest_parameters -> rest_parameters
         | [] -> [])
        rest
  in
  let lowered_arguments =
    preserve_before_prelude context (lower_arguments parameter_types arguments)
  in
  let call = D.DCallExpr (lowered_callee.result, results lowered_arguments) in
  let prelude = lowered_callee.prelude @ join_preludes lowered_arguments in
  let resolved_type = Sem.infer context.environment (Py.Call (callee, arguments)) in
  let effectful =
    lowered_callee.effectful
    || List.exists lowered_arguments ~f:(fun value -> value.effectful)
    || match Sem.callable_kind context.environment callee with
       | Sem.Method | Sem.Constructor | Sem.Generator -> true
       | Sem.PureFunction -> false
  in
  begin
    match context.evaluation, effectful with
    | Scoped, true -> raise (LoweringError "effectful calls are unsupported in scoped expressions")
    | _ -> ()
  end;
  match Sem.callable_kind context.environment callee, context.evaluation with
  | (Sem.Method | Sem.Generator), Eager ->
    let identifier = fresh_temp () in
    { prelude = prelude @ [ D.DAssignLvalue (None, [ D.Local identifier ], [ call ]) ]
    ; result = D.DIdentifier identifier
    ; resolved_type
    ; control_flow = false
    ; effectful
    }
  | _ ->
    { prelude; result = call; resolved_type; control_flow = false; effectful }

and lower_selector context = function
  | Py.Index index ->
    let lowered = lower context index in
    lowered, IndexSelector index
  | Py.Slice (lower_bound, upper_bound) ->
    let lowered_bounds = lower_many context (Option.to_list lower_bound @ Option.to_list upper_bound) in
    let lower_value =
      match lower_bound with
      | Some _ -> Some (List.hd_exn lowered_bounds)
      | None -> None
    in
    let upper_value =
      match upper_bound with
      | Some _ -> Some (List.last_exn lowered_bounds)
      | None -> None
    in
    let lower_result = Option.map lower_value ~f:(fun value -> value.result) in
    let upper_result = Option.map upper_value ~f:(fun value -> value.result) in
    let kind, arguments =
      match lower_result, upper_result with
      | Some lower_result, Some upper_result -> BothBounds, [ lower_result; upper_result ]
      | Some lower_result, None -> LowerBound, [ lower_result ]
      | None, Some upper_result -> UpperBound, [ upper_result ]
      | None, None -> NoBounds, []
    in
    let lowered = Option.to_list lower_value @ Option.to_list upper_value in
    ({ prelude = join_preludes lowered
     ; result = D.DSlice (lower_result, upper_result)
     ; resolved_type = Sem.infer context.environment (Py.Slice (None, None))
     ; control_flow = List.exists lowered ~f:(fun value -> value.control_flow)
     ; effectful = List.exists lowered ~f:(fun value -> value.effectful)
     }, SliceSelector (kind, arguments))
  | _ -> fail "subscript selector must be an index or slice"

and lower_subscript context value selector =
  let lowered_value = lower context value in
  let lowered_selector, source_selector = lower_selector context selector in
  let lowered_value =
    if is_eager context && not (List.is_empty lowered_selector.prelude) then
      materialize context lowered_value
    else lowered_value
  in
  let value_type = Sem.infer context.environment value in
  let name = generic_name value_type in
  let result_type = Sem.infer context.environment (Py.Subscript (value, selector)) in
  let result =
    match source_selector with
    | IndexSelector index ->
      begin
        match name with
        | "list" ->
          D.DCallExpr
            (D.DDot (lowered_value.result, (S.def_pos, Some "atIndex")),
             [ lowered_selector.result ])
        | "seq" | "array" | "map" -> D.DNativeIndex (lowered_value.result, lowered_selector.result)
        | "tuple" ->
          begin
            match Sem.integer_literal index with
            | Some position -> D.DTupleIndex (lowered_value.result, position)
            | None -> raise (LoweringError "tuple indexes must be statically known")
          end
        | _ -> D.DSubscript (lowered_value.result, lowered_selector.result)
      end
    | SliceSelector (kind, arguments) ->
      begin
        match name with
        | "list" ->
          let method_name =
            match kind with
            | BothBounds -> "range"
            | LowerBound -> "rangeLower"
            | UpperBound -> "rangeUpper"
            | NoBounds -> "rangeNone"
          in
          D.DCallExpr
            (D.DDot (lowered_value.result, (S.def_pos, Some method_name)), arguments)
        | _ -> D.DSubscript (lowered_value.result, lowered_selector.result)
      end
  in
  let prelude = lowered_value.prelude @ lowered_selector.prelude in
  let is_list_slice =
    match source_selector, name with
    | SliceSelector _, "list" -> true
    | _ -> false
  in
  match is_list_slice, context.evaluation with
  | true, Scoped -> fail "list slices are unsupported in scoped expressions"
  | true, Eager ->
    let identifier = fresh_temp () in
    { prelude = prelude @ [ D.DAssignLvalue (None, [ D.Local identifier ], [ result ]) ]
    ; result = D.DIdentifier identifier
    ; resolved_type = result_type
    ; control_flow = lowered_value.control_flow || lowered_selector.control_flow
    ; effectful = true
    }
  | false, _ ->
    { prelude
    ; result
    ; resolved_type = result_type
    ; control_flow = lowered_value.control_flow || lowered_selector.control_flow
    ; effectful = lowered_value.effectful || lowered_selector.effectful
    }

and lower_compare_chain context first comparisons =
  match comparisons with
  | [] -> fail "comparison chains require at least one comparison operator"
  | _ ->
    let lower_raw evaluation operand = lower evaluation operand in
    let lower_operand evaluation operand =
      try lower_raw evaluation operand with
      | LoweringError message -> fail ("comparison-chain operand: " ^ message)
    in
    let validate_operand _ lowered =
      if lowered.effectful then
        fail "effectful calls are unsupported in comparison chains"
    in
    let lower_initial operand =
      match context.evaluation with
      | Eager ->
        begin
          try lower_raw (scoped context) operand with
          | LoweringError _ -> lower_operand context operand
        end
      | Scoped -> lower_operand (scoped context) operand
    in
    let lowered_first = lower_initial first in
    validate_operand true lowered_first;
    let first_identifier = fresh_temp () in
    let initial_prelude = ref lowered_first.prelude in
    let rec chain current_identifier previous first_comparison comparisons =
      let operator, operand = List.hd_exn comparisons in
      let rest = List.tl_exn comparisons in
      let lowered =
        if first_comparison then lower_initial operand
        else lower_operand (scoped context) operand
      in
      if first_comparison then initial_prelude := !initial_prelude @ lowered.prelude;
      validate_operand first_comparison lowered;
      let next_identifier = fresh_temp () in
      match rest with
      | [] ->
        D.DLet
          ( next_identifier
          , lowered.result
          , binary_expression
              context.environment
              previous
              operator
              operand
              (D.DIdentifier current_identifier)
              (D.DIdentifier next_identifier) )
      | _ ->
        let comparison =
          binary_expression
            context.environment
            previous
            operator
            operand
            (D.DIdentifier current_identifier)
            (D.DIdentifier next_identifier)
        in
        D.DLet
          ( next_identifier
          , lowered.result
          , D.DIfElseExpr (comparison, chain next_identifier operand false rest, D.DFalse) )
    in
    let result = D.DLet (first_identifier, lowered_first.result, chain first_identifier first true comparisons) in
    { prelude = !initial_prelude
    ; result
    ; resolved_type = Py.TBool S.def_seg
    ; control_flow = true
    ; effectful = false
    }

and lower_for context specifications identifiers iterable body =
  reserve_environment context.environment;
  List.iter specifications ~f:reserve_specification;
  List.iter identifiers ~f:reserve_segment;
  reserve_expression iterable;
  reserve_statements body;
  let lowered_iterable = lower context iterable in
  let iterable_type = Sem.infer context.environment iterable in
  let kind = Sem.collection_kind iterable_type in
  let snapshot = fresh_temp () in
  let snapshot_expression = D.DIdentifier snapshot in
  let snapshot_binding =
    D.DAssignLvalue (None, [ D.Local snapshot ], [ lowered_iterable.result ])
  in
  let target =
    match identifiers with
    | [ identifier ] -> identifier
    | _ -> raise (LoweringError "collection iteration requires one loop target")
  in
  let target_name = Option.value (snd target) ~default:"" in
  let element_type =
    match kind, Sem.collection_arguments iterable_type with
    | Sem.MapCollection, key :: _ -> key
    | _, element :: _ -> element
    | _ -> Py.TIdent S.def_seg
  in
  let loop_environment =
    Sem.enter_scope context.environment Sem.ComprehensionScope
    |> fun environment -> Sem.bind environment target_name element_type
  in
  let loop_context =
    let inherited_iterated_lists =
      List.filter context.iterated_lists ~f:(fun name -> not (String.equal name target_name))
    in
    let inherited_iterated_maps =
      List.filter context.iterated_maps ~f:(fun name -> not (String.equal name target_name))
    in
    let iterated_lists =
      match kind, iterable with
      | Sem.ListCollection, Py.Identifier source
        when not (String.equal (Option.value (snd source) ~default:"") target_name) ->
        Sem.list_may_aliases_for context.environment (Option.value (snd source) ~default:"")
        @ inherited_iterated_lists
      | _ -> inherited_iterated_lists
    in
    let iterated_maps =
      match kind, iterable with
      | Sem.MapCollection, Py.Identifier source
        when not (String.equal (Option.value (snd source) ~default:"") target_name) ->
        Sem.map_may_aliases_for context.environment (Option.value (snd source) ~default:"")
        @ inherited_iterated_maps
      | _ -> inherited_iterated_maps
    in
    { context with
      environment = loop_environment
    ; loop_depth = context.loop_depth + 1
    ; iterated_lists
    ; iterated_maps
    }
  in
  let lower_specs () =
    let lowered = List.map specifications ~f:(lower_loop_spec (scoped context))
    in
    List.concat_map lowered ~f:fst, List.map lowered ~f:snd
  in
  let target_lvalue = D.Local target in
  let lower_indexed_loop length element =
    let counter = fresh_temp () in
    let limit = fresh_temp () in
    let counter_expression = D.DIdentifier counter in
    let invariant =
      D.DInvariant
        (D.DBinary
           ( D.DBinary (D.DIntLit "0", D.DLEq S.def_seg, counter_expression)
           , D.DAnd S.def_seg
           , D.DBinary (counter_expression, D.DLEq S.def_seg, length) ))
    in
    let loop_body =
      [ D.DAssignLvalue (None, [ target_lvalue ], [ element counter_expression ])
      ; D.DAssignLvalue
          (None, [ D.Local counter ]
          , [ D.DBinary (counter_expression, D.DPlus S.def_seg, D.DIntLit "1") ]) ]
      @ lower_statements loop_context body
    in
    let user_prelude, user_specs = lower_specs () in
    lowered_iterable.prelude
    @ [ snapshot_binding ]
    @ user_prelude
      @ [ D.DAssignLvalue (None, [ D.Local counter ], [ D.DIntLit "0" ])
      ; D.DAssignLvalue (None, [ D.Local limit ], [ length ])
      ; D.DWhile (invariant :: user_specs, D.DBinary (counter_expression, D.DLt S.def_seg, length), loop_body) ]
  in
  let lower_value_loop initial =
    let remaining = fresh_temp () in
    let remaining_expression = D.DIdentifier remaining in
    let target_expression = D.DIdentifier target in
    let nonempty = D.DBinary (D.DLen (S.def_seg, remaining_expression), D.DGt S.def_seg, D.DIntLit "0") in
    let subset = D.DInvariant (D.DBinary (remaining_expression, D.DSetSubset S.def_seg, initial)) in
    let decreasing = D.DDecreases (D.DLen (S.def_seg, remaining_expression)) in
    let choose =
      D.DAssignSuchThat
        ( Some (type_dfy element_type)
        , target_lvalue
        , D.DBinary (target_expression, D.DIn S.def_seg, remaining_expression) )
    in
    let remove =
      D.DAssignLvalue
        ( None
        , [ D.Local remaining ]
        , [ D.DBinary (remaining_expression, D.DSetDifference S.def_seg, D.DSetExpr [ target_expression ]) ] )
    in
    let user_prelude, user_specs = lower_specs () in
    user_prelude
    @ [ D.DAssignLvalue (None, [ D.Local remaining ], [ initial ])
      ; D.DWhile
          ( subset :: decreasing :: user_specs
          , nonempty
          , choose :: remove :: lower_statements loop_context body ) ]
  in
  match kind with
  | Sem.ListCollection ->
    lower_indexed_loop
      (D.DLen
         ( S.def_seg
         , D.DDot (snapshot_expression, (S.def_pos, Some "lst")) ))
      (fun index -> D.DCallExpr (D.DDot (snapshot_expression, (S.def_pos, Some "atIndex")), [ index ]))
  | Sem.SequenceCollection ->
    lower_indexed_loop
      (D.DLen (S.def_seg, snapshot_expression))
      (fun index -> D.DNativeIndex (snapshot_expression, index))
  | Sem.SetCollection ->
    lowered_iterable.prelude @ [ snapshot_binding ] @ lower_value_loop snapshot_expression
  | Sem.MapCollection ->
    let lowered =
      lowered_iterable.prelude
      @ [ snapshot_binding ]
      @ lower_value_loop (D.DMapKeys snapshot_expression)
    in
    if context.check_map_iteration_order && Sem.map_iteration_is_order_sensitive body then
      raise (LoweringError "order-dependent behavior in map iteration is unsupported")
    else lowered
  | _ -> fail "for loop iterable is not a supported collection"

and lower_comprehension context expression =
  begin
    match context.evaluation with
    | Scoped -> raise (LoweringError (reject_scoped_comprehension ()))
    | Eager -> ()
  end;
  reserve_environment context.environment;
  reserve_expression expression;
  let accumulator = fresh_temp () in
  let accumulator_name = Option.value (snd accumulator) ~default:"" in
  let resolved_type = Sem.infer context.environment expression in
  let kind, source_clauses, source_result, source_key =
    match expression with
    | Py.ListComprehension (result, clauses) -> `List, clauses, result, None
    | Py.SetComprehension (result, clauses) -> `Set, clauses, result, None
    | Py.DictComprehension (key, value, clauses) -> `Dict, clauses, value, Some key
    | _ -> raise (LoweringError (reject_non_comprehension ()))
  in
  let initial_result, initial_type =
    match kind with
    | `List -> D.DNew (type_dfy resolved_type, [ D.DSeqExpr [] ]), resolved_type
    | `Set -> D.DSetExpr [], resolved_type
    | `Dict -> D.DMapExpr [], resolved_type
  in
  let accumulator_binding =
    D.DAssignLvalue (None, [ D.Local accumulator ], [ initial_result ])
  in
  let accumulator_environment = Sem.bind context.environment accumulator_name initial_type in
  let preserves_order = match kind with `List -> true | `Set | `Dict -> false in
  if Sem.comprehension_map_iteration_is_order_sensitive
       ~preserves_order
       context.environment source_result source_key source_clauses
  then raise (LoweringError "order-dependent behavior in map iteration is unsupported");
  let clauses, substitutions = rename_comprehension_clauses [] source_clauses in
  let result = rename_comprehension_expression substitutions source_result in
  let key = Option.map source_key ~f:(rename_comprehension_expression substitutions) in
  let append_body result =
    match kind with
    | `List ->
      [ Py.Exp
          (Py.Call
             ( Py.Dot (Py.Identifier accumulator, (S.def_pos, Some "append"))
             , [ result ] )) ]
    | `Set ->
      [ Py.Assign
          ( None
          , [ Py.Identifier accumulator ]
          , [ Py.BinaryExp
                ( Py.Identifier accumulator
                , Py.BitOr S.def_seg
                , Py.Set [ result ] ) ] ) ]
    | `Dict ->
      let key = Option.value_exn key in
      [ Py.Assign
          ( None
          , [ Py.Subscript (Py.Identifier accumulator, Py.Index key) ]
          , [ result ] ) ]
  in
  let rec build = function
    | [] -> append_body result
    | Py.ComprehensionFor (targets, iterable) :: rest ->
      [ Py.For ([], targets, iterable, build rest) ]
    | Py.ComprehensionIf condition :: rest ->
      [ Py.IfElse (condition, build rest, [], []) ]
  in
  let generated = build clauses in
  let body_context =
    { context with
      environment = accumulator_environment
    ; check_map_iteration_order = false
    }
  in
  let lowered_body = lower_statements body_context generated in
  { prelude = accumulator_binding :: lowered_body
  ; result = D.DIdentifier accumulator
  ; resolved_type
  ; control_flow = true
  ; effectful = true
  }

and lower context expression =
  let environment = context.environment in
  match expression with
  | Py.Typ typ ->
    begin
      match typ with
      | Py.TNone _ -> { prelude = []; result = D.DNull; resolved_type = Sem.normalize_type typ; control_flow = false; effectful = false }
      | _ -> fail "Type in expression context only allowed as right-hand-side of assignment"
    end
  | Py.Literal literal ->
    { prelude = []; result = literal_dfy literal; resolved_type = Sem.infer environment expression; control_flow = false; effectful = false }
  | Py.Identifier identifier ->
    { prelude = []; result = D.DIdentifier identifier; resolved_type = Sem.infer environment expression; control_flow = false; effectful = false }
  | Py.Dot (value, identifier) ->
    let lowered = lower context value in
    { prelude = lowered.prelude
    ; result = D.DDot (lowered.result, identifier)
    ; resolved_type = Sem.infer environment expression
    ; control_flow = lowered.control_flow
    ; effectful = lowered.effectful
    }
  | Py.BinaryExp (left, operator, right) ->
    let left_context = context in
    let right_context =
      match operator with
      | Py.And _ | Py.Or _ -> scoped context
      | _ -> context
    in
    let lowered_left = lower left_context left in
    let lowered_right = lower right_context right in
    let lowered_left =
      if is_eager context && not (List.is_empty lowered_right.prelude) then
        materialize context lowered_left
      else lowered_left
    in
    { prelude = lowered_left.prelude @ lowered_right.prelude
    ; result = binary_expression environment left operator right lowered_left.result lowered_right.result
    ; resolved_type = Sem.infer environment expression
    ; control_flow = lowered_left.control_flow || lowered_right.control_flow
    ; effectful = lowered_left.effectful || lowered_right.effectful
    }
  | Py.UnaryExp (operator, value) ->
    let lowered = lower context value in
    { prelude = lowered.prelude
    ; result = D.DUnary (unary_operator operator, lowered.result)
    ; resolved_type = Sem.infer environment expression
    ; control_flow = lowered.control_flow
    ; effectful = lowered.effectful
    }
  | Py.Call (callee, arguments) -> lower_call context callee arguments
  | Py.CompareChain (first, comparisons) -> lower_compare_chain context first comparisons
  | Py.Lst elements -> lower_list context elements
  | Py.Array elements -> lower_collection context (fun values -> D.DArrayExpr values) elements (Sem.infer environment expression)
  | Py.Set elements -> lower_collection context (fun values -> D.DSetExpr values) elements (Sem.infer environment expression)
  | Py.Dict entries -> lower_map context entries
  | Py.ListComprehension _ | Py.SetComprehension _ | Py.DictComprehension _ ->
    lower_comprehension context expression
  | Py.Tuple elements ->
    begin
      match elements with
      | [ element ] -> lower context element
      | _ -> lower_collection context (fun values -> D.DTupleExpr values) elements (Sem.infer environment expression)
    end
  | Py.SingletonTuple (_, element) -> lower context element
  | Py.Subscript (value, selector) -> lower_subscript context value selector
  | Py.Index value -> lower context value
  | Py.Slice (lower_bound, upper_bound) ->
    fst (lower_selector context (Py.Slice (lower_bound, upper_bound)))
  | Py.Forall (identifiers, body) ->
    let lowered = lower (scoped context) body in
    { prelude = []; result = D.DForall (identifiers, lowered.result); resolved_type = Py.TBool S.def_seg; control_flow = true; effectful = lowered.effectful }
  | Py.Exists (identifiers, body) ->
    let lowered = lower (scoped context) body in
    { prelude = []; result = D.DExists (identifiers, lowered.result); resolved_type = Py.TBool S.def_seg; control_flow = true; effectful = lowered.effectful }
  | Py.Len (segment, value) ->
    let lowered = lower (scoped context) value in
    let result =
      match generic_name (Sem.infer environment value) with
      | "list" -> D.DCallExpr (D.DDot (lowered.result, (fst segment, Some "len")), [])
      | _ -> D.DLen (segment, lowered.result)
    in
    { prelude = lowered.prelude; result; resolved_type = Py.TInt S.def_seg; control_flow = lowered.control_flow; effectful = lowered.effectful }
  | Py.Max (segment, value) ->
    let lowered = lower context value in
    { prelude = lowered.prelude
    ; result = D.DCallExpr (D.DDot (lowered.result, segment), [])
    ; resolved_type = Sem.infer environment expression
    ; control_flow = lowered.control_flow
    ; effectful = lowered.effectful
    }
  | Py.Old (segment, value) ->
    let lowered = lower (scoped context) value in
    { prelude = []; result = D.DOld (segment, lowered.result); resolved_type = Sem.infer environment expression; control_flow = true; effectful = lowered.effectful }
  | Py.Fresh (segment, value) ->
    let lowered = lower (scoped context) value in
    { prelude = []; result = D.DFresh (segment, lowered.result); resolved_type = Sem.infer environment expression; control_flow = true; effectful = lowered.effectful }
  | Py.Lambda (identifiers, body) ->
    let lowered = lower (scoped context) body in
    let parameters = List.map identifiers ~f:(fun identifier -> identifier, D.DVoid) in
    { prelude = []; result = D.DLambda (parameters, [], lowered.result); resolved_type = Sem.infer environment expression; control_flow = true; effectful = lowered.effectful }
  | Py.IfElseExp (when_true, condition, when_false) ->
    let lowered_condition = lower context condition in
    let lowered_true = lower (scoped context) when_true in
    let lowered_false = lower (scoped context) when_false in
    { prelude = lowered_condition.prelude
    ; result = D.DIfElseExpr (lowered_condition.result, lowered_true.result, lowered_false.result)
    ; resolved_type = Sem.infer environment expression
    ; control_flow = true
    (* Branches are lowered in [Scoped] mode, which rejects effectful calls
       before a result can be constructed.  Only the eager condition can
       therefore contribute an effect to this expression. *)
    ; effectful = lowered_condition.effectful
    }

and lower_spec context = function
  | Py.Pre value -> let lowered = lower (scoped context) value in lowered.prelude, D.DRequires lowered.result
  | Py.Post value -> let lowered = lower (scoped context) value in lowered.prelude, D.DEnsures lowered.result
  | Py.Invariant value -> let lowered = lower (scoped context) value in lowered.prelude, D.DInvariant lowered.result
  | Py.Decreases value -> let lowered = lower (scoped context) value in lowered.prelude, D.DDecreases lowered.result
  | Py.Reads value -> let lowered = lower (scoped context) value in lowered.prelude, D.DReads lowered.result
  | Py.Modifies value -> let lowered = lower (scoped context) value in lowered.prelude, D.DModifies lowered.result

and lower_loop_spec context = function
  | Py.Invariant value -> let lowered = lower (scoped context) value in lowered.prelude, D.DInvariant lowered.result
  | Py.Decreases value -> let lowered = lower (scoped context) value in lowered.prelude, D.DDecreases lowered.result
  | Py.Pre _ | Py.Post _ | Py.Reads _ | Py.Modifies _ ->
    fail "loop specifications support only invariant and decreases"

and lower_lvalue context target =
  match target with
  | Py.Identifier identifier -> { prelude = []; target = D.Local identifier }
  | Py.Dot (value, identifier) ->
    let lowered = lower (scoped context) value in
    { prelude = lowered.prelude; target = D.Field (lowered.result, identifier) }
  | Py.Subscript (value, Py.Index index) ->
    let lowered_value = lower (scoped context) value in
    let lowered_index = lower (scoped context) index in
    { prelude = lowered_value.prelude @ lowered_index.prelude
    ; target = D.Index (lowered_value.result, lowered_index.result)
    }
  | Py.Tuple targets ->
    let lowered = List.map targets ~f:(lower_lvalue context) in
    { prelude = List.concat_map lowered ~f:(fun value -> value.prelude)
    ; target = D.TupleTarget (List.map lowered ~f:(fun value -> value.target))
    }
  | _ -> fail "assignment target is not an explicit lvalue"

and lower_expression_statement context expression =
  match expression with
  | Py.Call (Py.Identifier identifier, arguments)
    when List.mem [ "set"; "setf"; "dict"; "dictf"; "map" ]
           (Option.value (snd identifier) ~default:"" |> String.lowercase)
           ~equal:String.equal ->
    let lowered = lower_call context (Py.Identifier identifier) arguments in
    lowered.prelude, []
  | Py.Call (callee, arguments) ->
    reject_iterated_list_mutation context callee;
    let lowered_callee = lower context callee in
    let lowered_arguments = lower_many context arguments in
    lowered_callee.prelude @ join_preludes lowered_arguments,
    [ D.DCallStmt (lowered_callee.result, results lowered_arguments) ]
  | _ ->
    let lowered = lower context expression in
    lowered.prelude, [ D.DAssert lowered.result ]

and lower_map_assignment context map key value =
  let map_expression = Py.Identifier map in
  begin
    match Sem.collection_kind (Sem.infer context.environment map_expression) with
    | Sem.MapCollection -> ()
    | _ -> raise (LoweringError "indexed assignment target is not a map")
  end;
  begin
    match List.exists context.iterated_maps ~f:(String.equal (Option.value (snd map) ~default:"")) with
    | true -> raise (LoweringError "map updates while iterating are unsupported")
    | false -> ()
  end;
  let lowered_value = lower context value in
  let lowered_key = lower context key in
  lowered_value.prelude
  @ lowered_key.prelude
  @ [ D.DAssignLvalue
        ( None
        , [ D.Local map ]
        , [ D.DMapUpdate (D.DIdentifier map, lowered_key.result, lowered_value.result) ] ) ]

and lower_assignment context annotation targets values =
  let lower_regular_assignment () =
    let value_context =
      match annotation, values with
      | Some annotation, [ _ ] ->
        with_expected_type context (Sem.normalize_type (annotation_type annotation))
      | _ -> context
    in
    let lowered_values = lower_many value_context values in
    let lowered_targets = List.map targets ~f:(lower_lvalue context) in
    let type_annotation =
      Option.map annotation ~f:(fun value ->
        type_dfy (Sem.normalize_type (annotation_type value)))
    in
    join_preludes lowered_values
    @ List.concat_map lowered_targets ~f:(fun value -> value.prelude)
    @ [ D.DAssignLvalue
          (type_annotation, List.map lowered_targets ~f:(fun value -> value.target),
           results lowered_values) ]
  in
  match targets, values with
  | [ Py.Subscript (Py.Identifier map, Py.Index key) ], [ value ] ->
    begin
      match Sem.collection_kind (Sem.infer context.environment (Py.Identifier map)) with
      | Sem.MapCollection -> lower_map_assignment context map key value
      | Sem.ListCollection -> reject_list_assignment ()
      | _ -> lower_regular_assignment ()
    end
  | _ -> lower_regular_assignment ()

and statements ?(environment = Sem.empty) ?return_type statements =
  reset ();
  reserve_environment environment;
  reserve_statements statements;
  let context =
    Option.value_map return_type ~default:(context environment)
      ~f:(with_return_type (context environment))
  in
  lower_statements context statements

and lower_statements context statements =
  let environment_after_statement environment statement =
    (* The semantic pass has already validated complete programs.  Replaying
       one statement here gives lowering the environment at the statement's
       actual source position, while retaining the old standalone lowering
       API for callers that intentionally provide partially typed trees. *)
    try Sem.validate_statements environment [ statement ] with
    | Sem.SemanticError _ -> environment
  in
  let rec lower_sequence context = function
    | [] -> []
    | statement :: rest ->
      let lowered = lower_statement context statement in
      let environment = environment_after_statement context.environment statement in
      lowered @ lower_sequence { context with environment } rest
  in
  lower_sequence context statements

and lower_statement context statement =
  match statement with
  | Py.Pass -> [ D.DEmptyStmt ]
  | Py.Break -> [ D.DBreak ]
  | Py.Continue ->
    if context.loop_depth > 0 then [ D.DContinue ]
    else fail "continue statements are only supported inside loops"
  | Py.Exp expression ->
    let prelude, statements = lower_expression_statement context expression in
    prelude @ statements
  | Py.Assert expression ->
    let lowered = lower context expression in
    lowered.prelude @ [ D.DAssert lowered.result ]
  | Py.Return expression ->
    let context =
      Option.value_map context.return_type ~default:context ~f:(with_expected_type context)
    in
    let lowered = lower context expression in
    lowered.prelude @ [ D.DReturn [ lowered.result ] ]
  | Py.Assign (annotation, targets, values) ->
    lower_assignment context annotation targets values
  | Py.IfElse (condition, first, alternatives, last) ->
    let lowered_condition = lower context condition in
    let first = lower_statements context first in
    let alternatives = List.map alternatives ~f:(fun (condition, body) ->
      let lowered = lower context condition in
      lowered.prelude, lowered.result, lower_statements context body) in
    let last = lower_statements context last in
    if List.for_all alternatives ~f:(fun (prelude, _, _) -> List.is_empty prelude) then
      lowered_condition.prelude
      @ [ D.DIf
            ( lowered_condition.result
            , first
            , List.map alternatives ~f:(fun (_, condition, body) -> condition, body)
            , last ) ]
    else
      let rec nested = function
        | [] -> last
        | (prelude, condition, body) :: rest ->
          prelude @ [ D.DIf (condition, body, [], nested rest) ]
      in
      lowered_condition.prelude @ [ D.DIf (lowered_condition.result, first, [], nested alternatives) ]
  | Py.While (specifications, condition, body) ->
    let lowered_condition = lower context condition in
    let specifications = List.map specifications ~f:(lower_loop_spec (scoped context)) in
    let spec_prelude = List.concat_map specifications ~f:fst in
    let specifications = List.map specifications ~f:snd in
    let body = lower_statements { context with loop_depth = context.loop_depth + 1 } body in
    if List.is_empty lowered_condition.prelude then
      spec_prelude @ [ D.DWhile (specifications, lowered_condition.result, body) ]
    else
      let guard =
        D.DIf
          ( D.DUnary (D.DNot S.def_seg, lowered_condition.result)
          , [ D.DBreak ]
          , []
          , [] )
      in
      spec_prelude
      @ [ D.DWhile (specifications, D.DTrue, lowered_condition.prelude @ [ guard ] @ body) ]
  | Py.For (specifications, identifiers, iterable, body) ->
    lower_for context specifications identifiers iterable body
  | Py.Function _ -> fail "nested function declarations are not Dafny statements"

let expression ?(environment = Sem.empty) ?expected_type expression =
  reset ();
  reserve_environment environment;
  reserve_expression expression;
  let context =
    Option.value_map expected_type ~default:(context environment) ~f:(with_expected_type (context environment))
  in
  lower context expression
