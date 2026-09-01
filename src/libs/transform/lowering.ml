open Base

module Py = Pyparse.Astpy
module D = Astdfy
module S = Pyparse.Sourcemap
module Sem = Semantic

type evaluation = Eager | Scoped

type context =
  { environment : Sem.environment
  ; evaluation : evaluation
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

let reset () = temp_number := 0

let fresh_temp () =
  Int.incr temp_number;
  (S.def_pos, Some ("lowered_" ^ Int.to_string !temp_number))

let context environment = { environment; evaluation = Eager }

let scoped context = { context with evaluation = Scoped }

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

let join_preludes (lowered : lowered list) =
  List.concat_map lowered ~f:(fun value -> value.prelude)

let results (lowered : lowered list) = List.map lowered ~f:(fun value -> value.result)

let rec lower_many context expressions = List.map expressions ~f:(lower context)

and lower_collection context constructor expressions resolved_type =
  let lowered = lower_many context expressions in
  { prelude = join_preludes lowered
  ; result = constructor (results lowered)
  ; resolved_type
  ; control_flow = List.exists lowered ~f:(fun value -> value.control_flow)
  ; effectful = List.exists lowered ~f:(fun value -> value.effectful)
  }

and lower_list context elements =
  let lowered = lower_many context elements in
  match context.evaluation with
  | Scoped -> fail "list literals cannot be constructed inside a scoped expression"
  | Eager ->
    let identifier = fresh_temp () in
    let resolved_type = Sem.infer context.environment (Py.Lst elements) in
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

and lower_call context callee arguments =
  let lowered_callee = lower context callee in
  let lowered_arguments = lower_many context arguments in
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
    let lower_value = Option.map lower_bound ~f:(lower context) in
    let upper_value = Option.map upper_bound ~f:(lower context) in
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
  { prelude = lowered_value.prelude @ lowered_selector.prelude
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
    let first_identifier = fresh_temp () in
    let effectful = ref lowered_first.effectful in
    let initial_prelude = ref lowered_first.prelude in
    let rec chain current_identifier first_comparison comparisons =
      let operator, operand = List.hd_exn comparisons in
      let rest = List.tl_exn comparisons in
      let lowered =
        if first_comparison then lower_initial operand
        else lower_operand (scoped context) operand
      in
      if first_comparison then initial_prelude := !initial_prelude @ lowered.prelude;
      effectful := !effectful || lowered.effectful;
      let next_identifier = fresh_temp () in
      match rest with
      | [] ->
        D.DLet
          ( next_identifier
          , lowered.result
          , D.DBinary
              ( D.DIdentifier current_identifier
              , binary_operator operator
              , D.DIdentifier next_identifier ) )
      | _ ->
        let comparison =
          D.DBinary
            ( D.DIdentifier current_identifier
            , binary_operator operator
            , D.DIdentifier next_identifier )
        in
        D.DLet
          ( next_identifier
          , lowered.result
          , D.DIfElseExpr (comparison, chain next_identifier false rest, D.DFalse) )
    in
    let result = D.DLet (first_identifier, lowered_first.result, chain first_identifier true comparisons) in
    { prelude = !initial_prelude
    ; result
    ; resolved_type = Py.TBool S.def_seg
    ; control_flow = true
    ; effectful = !effectful
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
    { prelude = lowered_left.prelude @ lowered_right.prelude
    ; result = D.DBinary (lowered_left.result, binary_operator operator, lowered_right.result)
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
  | Py.Dict entries ->
    let lowered = List.map entries ~f:(fun (key, value) -> lower context key, lower context value) in
    let key_values = List.map lowered ~f:(fun (key, value) -> key.result, value.result) in
    { prelude = List.concat_map lowered ~f:(fun (key, value) -> key.prelude @ value.prelude)
    ; result = D.DMapExpr key_values
    ; resolved_type = Sem.infer environment expression
    ; control_flow = List.exists lowered ~f:(fun (key, value) -> key.control_flow || value.control_flow)
    ; effectful = List.exists lowered ~f:(fun (key, value) -> key.effectful || value.effectful)
    }
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
    ; effectful = lowered_condition.effectful || lowered_true.effectful || lowered_false.effectful
    }

let expression ?(environment = Sem.empty) expression =
  reset ();
  lower (context environment) expression

let lower_spec context = function
  | Py.Pre value -> let lowered = lower (scoped context) value in lowered.prelude, D.DRequires lowered.result
  | Py.Post value -> let lowered = lower (scoped context) value in lowered.prelude, D.DEnsures lowered.result
  | Py.Invariant value -> let lowered = lower (scoped context) value in lowered.prelude, D.DInvariant lowered.result
  | Py.Decreases value -> let lowered = lower (scoped context) value in lowered.prelude, D.DDecreases lowered.result
  | Py.Reads value -> let lowered = lower (scoped context) value in lowered.prelude, D.DReads lowered.result
  | Py.Modifies value -> let lowered = lower (scoped context) value in lowered.prelude, D.DModifies lowered.result

let rec lower_lvalue context target =
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

let lower_expression_statement context expression =
  match expression with
  | Py.Call (callee, arguments) ->
    let lowered_callee = lower context callee in
    let lowered_arguments = lower_many context arguments in
    lowered_callee.prelude @ join_preludes lowered_arguments,
    [ D.DCallStmt (lowered_callee.result, results lowered_arguments) ]
  | _ ->
    let lowered = lower context expression in
    lowered.prelude, [ D.DAssert lowered.result ]

let rec statements ?(environment = Sem.empty) statements =
  reset ();
  lower_statements (context environment) statements

and lower_statements context statements =
  List.concat_map statements ~f:(lower_statement context)

and lower_statement context statement =
  match statement with
  | Py.Pass -> [ D.DEmptyStmt ]
  | Py.Break -> [ D.DBreak ]
  | Py.Continue -> fail "continue statements are not supported"
  | Py.Exp expression ->
    let prelude, statements = lower_expression_statement context expression in
    prelude @ statements
  | Py.Assert expression ->
    let lowered = lower context expression in
    lowered.prelude @ [ D.DAssert lowered.result ]
  | Py.Return expression ->
    let lowered = lower context expression in
    lowered.prelude @ [ D.DReturn [ lowered.result ] ]
  | Py.Assign (annotation, targets, values) ->
    let lowered_values = lower_many context values in
    let lowered_targets = List.map targets ~f:(lower_lvalue context) in
    let type_annotation = Option.map annotation ~f:(fun value -> type_dfy (Sem.normalize_type (annotation_type value))) in
    join_preludes lowered_values
    @ List.concat_map lowered_targets ~f:(fun value -> value.prelude)
    @ [ D.DAssignLvalue (type_annotation, List.map lowered_targets ~f:(fun value -> value.target), results lowered_values) ]
  | Py.IfElse (condition, first, alternatives, last) ->
    let lowered_condition = lower context condition in
    let first = lower_statements context first in
    let alternatives = List.map alternatives ~f:(fun (condition, body) ->
      let lowered = lower context condition in
      lowered.prelude, lowered.result, lower_statements context body) in
    let alternatives = List.map alternatives ~f:(fun (prelude, condition, body) ->
      if List.is_empty prelude then condition, body
      else condition, prelude @ body) in
    lowered_condition.prelude @ [ D.DIf (lowered_condition.result, first, alternatives, lower_statements context last) ]
  | Py.While (specifications, condition, body) ->
    let lowered_condition = lower context condition in
    let specifications = List.map specifications ~f:(lower_spec (scoped context)) in
    let spec_prelude = List.concat_map specifications ~f:fst in
    let specifications = List.map specifications ~f:snd in
    lowered_condition.prelude @ spec_prelude @ [ D.DWhile (specifications, lowered_condition.result, lower_statements context body) ]
  | Py.For _ -> fail "for loops must be lowered before expression lowering"
  | Py.Function _ -> fail "nested function declarations are not Dafny statements"
