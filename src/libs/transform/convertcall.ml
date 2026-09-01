open Base
open Pyparse.Astpy
open Pyparse.Sourcemap

let temp_source = Hashtbl.create (module String)
let printf = Stdlib.Printf.printf
let var_num : int ref = ref 0

let reset () =
  Hashtbl.clear temp_source;
  var_num := 0

let replace e call =
  let pos, v = begin 
    match e with
    | Identifier ident -> ident
    | Dot (_, ident) -> ident
    | Call _ -> def_seg
    | Subscript _ -> def_seg
    | IfElseExp _ -> def_seg
    | _ -> failwith "primary of call can only be an identifier or dot expression" (* TODO: add segments other primaries *)
    end in
  let name = var_num := !var_num + 1; "tempcall_" ^ (Int.to_string !var_num) in
  let _ = begin
    match v with 
    | Some v -> Hashtbl.add temp_source ~key:name ~data:v
    | None -> Hashtbl.add temp_source ~key:name ~data:name
  end in
  let a_ident = (pos, Some name) in 
  (Assign (None, [Identifier a_ident], [call]), Identifier a_ident) (* TODO: use type of call *)

(* Traverse expressions under lexical binders without extracting assignments.
   This keeps the old conversion API safe for callers that still use it while
   making its traversal complete for every expression constructor. *)
let rec exp_calls_scoped = function
  | Dot (value, identifier) -> Dot (exp_calls_scoped value, identifier)
  | BinaryExp (left, operator, right) ->
    BinaryExp (exp_calls_scoped left, operator, exp_calls_scoped right)
  | CompareChain (first, comparisons) ->
    CompareChain
      ( exp_calls_scoped first
      , List.map comparisons ~f:(fun (operator, operand) -> operator, exp_calls_scoped operand) )
  | UnaryExp (operator, value) -> UnaryExp (operator, exp_calls_scoped value)
  | Call (callee, arguments) ->
    Call (exp_calls_scoped callee, List.map arguments ~f:exp_calls_scoped)
  | Lst values -> Lst (List.map values ~f:exp_calls_scoped)
  | Array values -> Array (List.map values ~f:exp_calls_scoped)
  | Set values -> Set (List.map values ~f:exp_calls_scoped)
  | Dict entries ->
    Dict (List.map entries ~f:(fun (key, value) -> exp_calls_scoped key, exp_calls_scoped value))
  | Tuple values -> Tuple (List.map values ~f:exp_calls_scoped)
  | SingletonTuple (comma, value) -> SingletonTuple (comma, exp_calls_scoped value)
  | Subscript (value, selector) -> Subscript (exp_calls_scoped value, exp_calls_scoped selector)
  | Index value -> Index (exp_calls_scoped value)
  | Slice (lower, upper) ->
    Slice (Option.map lower ~f:exp_calls_scoped, Option.map upper ~f:exp_calls_scoped)
  | Forall (identifiers, body) -> Forall (identifiers, exp_calls_scoped body)
  | Exists (identifiers, body) -> Exists (identifiers, exp_calls_scoped body)
  | Len (segment, value) -> Len (segment, exp_calls_scoped value)
  | Max (segment, value) -> Max (segment, exp_calls_scoped value)
  | Old (segment, value) -> Old (segment, exp_calls_scoped value)
  | Fresh (segment, value) -> Fresh (segment, exp_calls_scoped value)
  | Lambda (identifiers, body) -> Lambda (identifiers, exp_calls_scoped body)
  | IfElseExp (when_true, condition, when_false) ->
    IfElseExp
      (exp_calls_scoped when_true, exp_calls_scoped condition, exp_calls_scoped when_false)
  | expression -> expression

let rec exp_calls = function
  | Dot (e, ident) -> let al, n_e = exp_calls e in (al, Dot (n_e, ident))
  | BinaryExp (e1, op, e2) -> 
    let al1, n_e1 = exp_calls e1 in
    let al2, n_e2 = exp_calls e2 in
    (al1@al2, BinaryExp (n_e1, op, n_e2))
  | CompareChain (first, comparisons) ->
    [], CompareChain
      ( exp_calls_scoped first
      , List.map comparisons ~f:(fun (operator, operand) -> operator, exp_calls_scoped operand) )
  | UnaryExp (op, e) -> let al, n_e = exp_calls e in (al, UnaryExp (op, n_e))
  | Call (e, el) -> (* handle recursive case *)
    let al, n_e = exp_calls e in
    let als_nes = List.map ~f:exp_calls el in
    let n_el = List.fold als_nes ~f:(fun so_far (_, n_e) -> so_far@[n_e]) ~init:[] in
    let als = List.fold als_nes ~f:(fun so_far (al, _) -> so_far@al) ~init:[] in
    let a, a_ident = replace e (Call (n_e, n_el)) in 
    (al@als@[a], a_ident)
  | Lst el -> 
    let als_nes = List.map ~f:exp_calls el in
    let al, n_el =
      List.fold als_nes
        ~f:(fun (al1, n_el) (al2, e) -> (al1 @ al2, n_el @ [ e ]))
        ~init:([], [])
    in
    (al, Lst n_el)
  | Tuple el -> 
    let als_nes = List.map ~f:exp_calls el in
    let al, n_el =
      List.fold als_nes
        ~f:(fun (al1, n_el) (al2, e) -> (al1 @ al2, n_el @ [ e ]))
        ~init:([], [])
    in
    (al, Tuple n_el)
  | SingletonTuple (comma, value) ->
    let al, value = exp_calls value in
    (al, SingletonTuple (comma, value))
  | Subscript (e1, e2) -> 
    let al1, n_e1 = exp_calls e1 in
    let al2, n_e2 = exp_calls e2 in
    (al1@al2, Subscript (n_e1, n_e2))
  | Index e -> let al, n_e = exp_calls e in (al, Index n_e)
  | Slice (e1, e2) -> begin
      match e1, e2 with
      | Some r1, Some r2 -> 
        let al1, n_r1 = exp_calls r1 in
        let al2, n_r2 = exp_calls r2 in
        (al1@al2, Slice (Some n_r1, Some n_r2))
      | Some r1, None ->
        let al1, n_r1 = exp_calls r1 in
        (al1, Slice (Some n_r1, None))
      | None, Some r2 -> 
        let al2, n_r2 = exp_calls r2 in
        (al2, Slice (None, Some n_r2))
      | None, None -> ([], Slice (None, None))
    end
  | Len (s, e) -> let al, n_e = exp_calls e in (al, Len (s, n_e))
  | Old (s, e) -> let al, n_e = exp_calls e in (al, Old (s, n_e))
  | Fresh (s, e) -> let al, n_e = exp_calls e in (al, Fresh (s, n_e))
  | IfElseExp (e1, c, e2) -> 
    let al1, n_e1 = exp_calls e1 in
    let al2, n_c = exp_calls c in
    let al3, n_e2 = exp_calls e2 in
    (al1@al2@al3, IfElseExp (n_e1, n_c, n_e2))
  | Forall (identifiers, body) -> Forall (identifiers, exp_calls_scoped body) |> fun expression -> [], expression
  | Exists (identifiers, body) -> Exists (identifiers, exp_calls_scoped body) |> fun expression -> [], expression
  | Lambda (identifiers, body) -> Lambda (identifiers, exp_calls_scoped body) |> fun expression -> [], expression
  | Array values -> [], Array (List.map values ~f:exp_calls_scoped)
  | Set values -> [], Set (List.map values ~f:exp_calls_scoped)
  | Dict entries ->
    [], Dict (List.map entries ~f:(fun (key, value) -> exp_calls_scoped key, exp_calls_scoped value))
  | Max (segment, value) -> [], Max (segment, exp_calls_scoped value)
  | e -> ([], e) 
  
let assign_to_inv = function
  | (Assign (_, il, el)) -> 
    let res = begin
      List.map2 il el ~f:(fun e1 e2 ->
      Invariant (BinaryExp (e1, EqEq def_seg, e2)))
    end in
    begin match res with
    | Ok invl -> invl
    | Unequal_lengths -> failwith "unequal number of assignment expressions and targets"
    end
  | _ -> failwith ""

let spec_calls = function
  | Pre e -> let al, n_e = exp_calls e in (al, [Pre n_e])
  | Post e -> let al, n_e = exp_calls e in (al, [Post n_e])
  | Invariant e -> let al, n_e = exp_calls e in
    let al_invs = List.fold al ~f:(fun so_far a -> so_far@(assign_to_inv a)) ~init:[] in 
    (al, al_invs@[Invariant n_e])
  | Decreases e -> let al, n_e = exp_calls e in (al, [Decreases n_e])
  | Reads e -> let al, n_e = exp_calls e in (al, [Reads n_e])
  | Modifies e -> let al, n_e = exp_calls e in (al, [Modifies n_e])

let rec stmt_calls s = 
  match s with
  | Pass -> [s]
  | Break -> [s]
  | Continue -> [s]
  | Exp e -> let al, n_e = exp_calls e in al@[Exp n_e]
  | Assign (t, il, el) -> 
    let als_nes = List.map ~f:exp_calls el in
    let n_el = List.fold als_nes ~f:(fun so_far (_, n_e) -> so_far@[n_e]) ~init:[] in
    let als = List.fold als_nes ~f:(fun so_far (al, _) -> so_far@al) ~init:[] in
    als@[Assign (t, il, n_el)]
  | IfElse(e, sl1, esl, sl3) -> 
    let al, n_e = exp_calls e in
    let n_sl1 = List.fold sl1 ~f:(fun so_far s -> so_far@(stmt_calls s)) ~init:[] in
    let res = List.map esl ~f:(fun (e, s) -> (exp_calls e, List.fold s ~f:(fun so_far s -> so_far@(stmt_calls s)) ~init:[])) in (* fold here to flatten list *)
    let als = List.fold res ~f:(fun so_far ((al,_), _) -> so_far@al) ~init:[] in
    let n_esl = List.fold res ~f:(fun so_far ((_, n_e), s) -> so_far@[(n_e, s)]) ~init:[] in
    let n_sl3 = List.fold sl3 ~f:(fun so_far s -> so_far@(stmt_calls s)) ~init:[] in
    al@als@[IfElse (n_e, n_sl1, n_esl, n_sl3)]
  | Return e -> 
    let al, n_e = exp_calls e in
    al@[Return n_e]
  | Assert e -> let al, n_e = exp_calls e in al@[Assert n_e]
  | While (specl, e, sl) ->
    let al, n_e = exp_calls e in
    let als_nspecll = List.map specl ~f:spec_calls in
    let n_specl = List.fold als_nspecll ~f:(fun so_far (_, specl) -> so_far@specl) ~init:[] in
    (* let n_specl = List.fold n_specll ~f:(fun so_far specl -> so_far@[specl]) ~init:[] in *)
    let als = List.fold als_nspecll ~f:(fun so_far (al, _) -> so_far@al) ~init:[] in
    let n_sl = List.fold sl ~f:(fun so_far s -> so_far@(stmt_calls s)) ~init:[] in
    al@als@[While (n_specl, n_e, n_sl @ als)]
  | Function (specl, i, pl, t, sl) ->
    (* Function specifications are evaluated in the function's scope.  Do
       not hoist their calls into declarations preceding the function. *)
    let n_sl = List.fold sl ~f:(fun so_far s -> so_far@(stmt_calls s)) ~init:[] in
    [Function (specl, i, pl, t, n_sl)]
  | For (specl, il, e, sl) ->
    let als_nspecl = List.map specl ~f:spec_calls in
    let n_specl = List.fold als_nspecl ~f:(fun so_far (_, specs) -> so_far @ specs) ~init:[] in
    let spec_assignments = List.fold als_nspecl ~f:(fun so_far (al, _) -> so_far @ al) ~init:[] in
    let al, n_e = exp_calls e in
    let n_sl = List.fold sl ~f:(fun so_far s -> so_far @ stmt_calls s) ~init:[] in
    spec_assignments @ al @ [For (n_specl, il, n_e, n_sl)]

let prog program =
  reset ();
  match program with
  | Program sl -> Program (List.fold sl ~f:(fun so_far s -> so_far@(stmt_calls s)) ~init:[])
