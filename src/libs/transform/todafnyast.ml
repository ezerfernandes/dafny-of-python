open Base

open Pyparse.Astpy
open Astdfy
(* open Typing *)
open Pyparse.Sourcemap

let printf = Stdlib.Printf.printf

exception ToDfyError of string
let[@inline] failwith msg = raise (ToDfyError msg)

let typ_idents = Hash_set.create (module String)

let reset () = Hash_set.clear typ_idents

let check_exp_typ = function
  | Typ t -> t
  | Identifier s -> TIdent s
  | _ -> failwith "Invalid type"

let rec typ_dfy = function 
  | TIdent s -> DIdentTyp (s, [])
  | TInt s -> DInt s
  | TFloat s -> DReal s 
  | TBool s -> DBool s
  | TStr s -> DString s
  | TNone _ -> DVoid
  | TObj s -> DObj s
  | TLst (s, ot) -> begin
    match ot with
    | Some t -> let r = typ_dfy t in DIdentTyp (s, [r])
    | None -> failwith "Please specify the exact sequence type"
    end
  | TSet (s, ot) -> begin
    match ot with
    | Some t -> let r = typ_dfy t in DSet(s, r)
    | None -> failwith "Please specify the exact set type"
    end
  | TDict (s, ot1, ot2) -> begin
    match ot1, ot2 with
    | Some t1, Some t2 -> let r1 = typ_dfy t1 in let r2 = typ_dfy t2 in DMap (s, r1, r2)
    | None, _ -> failwith "Please specify the exact map type"
    | _, None -> failwith "Please specify the exact map type"

    end
  | TTuple (s, olt) -> begin
    match olt with
    | Some tpl -> DTuple (s, List.map ~f:typ_dfy tpl) 
    | None -> DTuple (s, [])
    end
  | TCallable (s, tl, t) -> DFunTyp (s, List.map ~f:typ_dfy tl, typ_dfy t)
  | TType (_, ot) -> begin match ot with
    | Some t -> typ_dfy t
    | None -> failwith "Please specify the exact type"
    end
  | TGeneric (s, tl) -> DIdentTyp (s, List.map ~f:typ_dfy tl)

let ident_dfy = function
  | s -> s

let literal_dfy = function
  | TrueLit -> DTrue
  | FalseLit -> DFalse
  | IntLit i -> DIntLit i
  | FloatLit f -> DRealLit f
  | StringLit s -> DStringLit s
  | NoneLit -> DNull

let unaryop_dfy = function
  | Not s -> DNot s
  | UMinus s -> DMinus s

let binaryop_dfy = function 
  | NotIn s -> DNotIn s
  | In s -> DIn s
  | Plus s -> DPlus s
  | Minus s -> DMinus s
  | Times s -> DTimes s
  | Divide s -> DDivide s
  | Mod s -> DMod s
  | NEq s -> DNEq s
  | EqEq s -> DEq s
  | Lt s -> DLt s
  | LEq s -> DLEq s
  | Gt s -> DGt s
  | GEq s -> DGEq s
  | And s -> DAnd s
  | Or s -> DOr s
  | BiImpl s -> DBiImpl s
  | Implies s -> DImplies s
  | Explies s -> DExplies s
  
let rec exp_dfy e =
  (* (match check e (Bool default_segment) [] with | Some (_, ctx) -> print ctx | None -> ()); *)
  match e with
  | Identifier s -> DIdentifier s
  | Dot (e, ident) -> DDot (exp_dfy e, ident)
  | BinaryExp (e1, op, e2) -> DBinary ((exp_dfy e1), (binaryop_dfy op), (exp_dfy e2))
  | CompareChain (first, comparisons) ->
    let rec chain left = function
      | [] -> left
      | (operator, right)::rest ->
        let comparison = DBinary (left, binaryop_dfy operator, exp_dfy right) in
        begin
          match rest with
          | [] -> comparison
          | _ -> DBinary (comparison, DAnd def_seg, chain (exp_dfy right) rest)
        end
    in
    chain (exp_dfy first) comparisons
  | UnaryExp (op, e) -> DUnary ((unaryop_dfy op), (exp_dfy e))
  | Literal l -> literal_dfy l
  | Call (e, el) -> let d_args = List.map ~f:exp_dfy el in DCallExpr (exp_dfy e, d_args)
  | Lst el -> DSeqExpr (List.map ~f:exp_dfy el)
  | Array el -> DArrayExpr (List.map ~f:exp_dfy el)
  | Set el -> DSetExpr (List.map ~f:exp_dfy el)
  (* | SetComp el -> DSetCompExpr (List.map ~f:exp_dfy el) *)
  | Dict eel -> DMapExpr (List.map ~f:(fun (k,v) -> (exp_dfy k, exp_dfy v)) eel)
  | Tuple (e::[]) -> exp_dfy e (* Dafny does not have 1-tuples *)
  | Tuple el -> DTupleExpr (List.map ~f:exp_dfy el)  
  | SingletonTuple (_, e) -> exp_dfy e
  | Subscript (e1, e2) -> DSubscript (exp_dfy e1, exp_dfy e2)
  | Index e -> DIndex (exp_dfy e)
  | Slice (e1, e2) -> begin
    match e1, e2 with
    | Some r1, Some r2 -> DSlice (Some (exp_dfy r1), Some (exp_dfy r2))
    | Some r1, None -> DSlice (Some (exp_dfy r1), None)
    | None, Some r2 -> DSlice (None, Some (exp_dfy r2))
    | None, None -> DSlice (None, None)
    end
  | Forall (s, e) -> DForall (s, exp_dfy e)
  | Exists (s, e) -> DExists (s, exp_dfy e)
  | Len (s, e) -> DLen (s, exp_dfy e)
  | Max (s, e) -> DCallExpr (DDot (exp_dfy e, s), [])
  | Old (s, e) -> DOld (s, exp_dfy e)
  | Fresh (s, e) -> DFresh (s, exp_dfy e)
  | Typ t -> begin match t with 
    | TNone _ -> DNull 
    | _ -> failwith "Type in expression context only allowed as right-hand-side of assignment"
  end
  | Lambda (fl, e) -> let dfl = List.map ~f:(fun x -> (x, DVoid)) fl in DLambda (dfl, [], exp_dfy e)
  | IfElseExp (e1, c, e2) -> DIfElseExpr (exp_dfy c, exp_dfy e1, exp_dfy e2)

let spec_dfy = function
  | Pre c -> DRequires (exp_dfy c)
  | Post c -> DEnsures (exp_dfy c)
  | Invariant e -> DInvariant (exp_dfy e)
  | Decreases d -> DDecreases (exp_dfy d)
  | Reads e -> DReads (exp_dfy e)
  | Modifies e -> DModifies (exp_dfy e)

let param_dfy = function
  | (id, te) -> ((ident_dfy id), (typ_dfy (check_exp_typ te)))

let rec stmt_dfy = function
  | Exp (Call (e, el)) -> begin
      let d_el = List.map ~f:exp_dfy el in
      DCallStmt (exp_dfy e, d_el)
    end
  | Exp (Dot (e, ident)) -> DCallStmt (DDot (exp_dfy e, ident_dfy ident), [])
  | Assign (t, il, el) -> begin match t with 
    | Some (Typ t) -> DAssign (Some (typ_dfy t), List.map ~f:ident_dfy (idlst_to_id il), (List.map ~f:exp_dfy el))
    | Some (Identifier ident) -> DAssign (Some (DIdentTyp ((ident_dfy ident), [])), List.map ~f:ident_dfy (idlst_to_id il), (List.map ~f:exp_dfy el))
    | None -> DAssign (None, List.map ~f:ident_dfy (idlst_to_id il), (List.map ~f:exp_dfy el))
    | _ -> failwith "Invalid type of assignment"
    end
  | IfElse (e, sl1, esl, sl3) -> let d_esl = List.map ~f:(fun (e,sl) -> let d_e = exp_dfy e in (d_e, (List.map ~f:stmt_dfy sl))) esl in DIf(exp_dfy e, (List.map ~f:stmt_dfy sl1), d_esl, (List.map ~f:stmt_dfy sl3))
  | Return el -> DReturn [exp_dfy el]
  | Assert e -> DAssert (exp_dfy e)
  | Break -> DBreak
  | Continue -> failwith "continue statements are not supported"
  | Pass -> DEmptyStmt
  | While (speclst, e, sl) -> DWhile (List.map ~f:spec_dfy speclst, exp_dfy e, List.map ~f:stmt_dfy sl)
  | For _ -> failwith "for loops are not supported"
  | Function _  -> assert false
  | Exp _ -> failwith "non-call expressions are not allowed as statements"


let convert_typsyn id rhs =
  match id with
  | Identifier ident -> begin
    let ident_v = seg_val ident in begin
      match rhs with 
      | Typ t -> begin match t with | TNone _ -> None
        | _ -> Hash_set.add typ_idents ident_v; Some (DTypSynonym (ident_dfy ident, Some (typ_dfy t)))
      end
      | Identifier typ_ident -> begin 
          let s_typ = seg_val typ_ident in
          match Base.Hash_set.find typ_idents ~f:(fun s -> String.compare s s_typ = 0) with
          | Some _ -> Hash_set.add typ_idents ident_v; Some (DTypSynonym (ident_dfy ident, Some (typ_dfy (TIdent typ_ident))))
          | None -> None
        end
      | _ -> None
      end
    end
  | _ -> None

let is_toplevel = function
  | Function _ -> true
  | Assign (_, _, ((Typ (TNone _))::_)) -> false
  | Assign (_, _, ((Typ _)::_)) -> true
  | _ -> false

let toplevel_dfy generics = function
  | Function (speclst, i, pl, te, sl) -> let t = check_exp_typ te in
    [DMeth (List.map ~f:spec_dfy speclst, i, generics, List.map ~f:param_dfy pl, [typ_dfy t], Some (List.map ~f:stmt_dfy sl))]
  | Assign (_, il, el) -> begin
    match List.map2 ~f:convert_typsyn il el with
    | Ok typ_syns -> List.filter_map ~f:(fun x -> x) typ_syns
    | Unequal_lengths -> failwith "Number of left-hand identifiers must be equal to number of right-hand expressions"
    end
  | _ -> []

let func_dfy generics = function
  | Function (speclst, i, pl, te, (Return e)::[]) -> let t = check_exp_typ te in
    [DFuncMeth (List.map ~f:spec_dfy speclst, i, generics, List.map ~f:param_dfy pl, typ_dfy t, Some (exp_dfy e))]
  | Function (speclst, i, pl, te, (Exp e)::[]) -> let t = check_exp_typ te in
    [DFuncMeth (List.map ~f:spec_dfy speclst, i, generics, List.map ~f:param_dfy pl, typ_dfy t, Some (exp_dfy e))]
  | Function (speclst, i, pl, te, Pass::[]) -> let t = check_exp_typ te in
    [DFuncMeth (List.map ~f:spec_dfy speclst, i, generics, List.map ~f:param_dfy pl, typ_dfy t, None)]
  | _ -> []  

let is_func = function
  | Function (_, _, _, _, (Return _)::[]) -> true
  | Function (_, _, _, _, (Exp _)::[]) -> true
  | Function (_, _, _, _, Pass::[]) -> true
  | _ -> false

(* The semantic lowering path is intentionally kept alongside the original
   small conversion helpers.  The helpers remain useful as focused
   compatibility APIs, while complete programs use one recursive, typed
   expression pass so collections and calls cannot be skipped independently. *)
let semantic_function_env environment name parameters return_type =
  let scoped = Semantic.enter_scope environment (Semantic.FunctionScope (seg_val name)) in
  let parameters =
    List.map parameters ~f:(fun (identifier, value) ->
      seg_val identifier, Semantic.annotation value)
  in
  Semantic.bind_many scoped
    (parameters @ [ ("return", Semantic.annotation return_type) ])

let semantic_specs environment specifications =
  List.map specifications ~f:(fun specification ->
    let _, lowered = Lowering.lower_spec (Lowering.context environment) specification in
    lowered)

let semantic_params parameters =
  List.map parameters ~f:(fun (identifier, value) ->
    ident_dfy identifier, Lowering.type_dfy (Semantic.annotation value))

let semantic_function generics environment (speclst, name, parameters, return_type, body) =
  let function_environment = semantic_function_env environment name parameters return_type in
  let parameters = semantic_params parameters in
  let list_reads =
    List.filter_map parameters ~f:(fun (identifier, typ) ->
      match typ with
      | DIdentTyp ((_, Some name), _) when String.equal (String.lowercase name) "list" ->
        Some (DReads (DIdentifier identifier))
      | _ -> None)
  in
  let specifications = semantic_specs function_environment speclst @ list_reads in
  let return_type = Lowering.type_dfy (Semantic.annotation return_type) in
  match body with
  | [ Return expression ] | [ Exp expression ] ->
    let lowered = Lowering.expression ~environment:function_environment expression in
    if List.is_empty lowered.prelude && not lowered.effectful then
      DFuncMeth (specifications, name, generics, parameters, return_type, Some lowered.result)
    else
      DMeth
        (specifications, name, generics, parameters, [ return_type ],
         Some (lowered.prelude @ [ DReturn [ lowered.result ] ]))
  | [ Pass ] -> DFuncMeth (specifications, name, generics, parameters, return_type, None)
  | _ ->
    DMeth
      (specifications, name, generics, parameters, [ return_type ],
       Some (Lowering.statements ~environment:function_environment body))

let semantic_toplevel generics environment statement =
  match statement with
  | Function (speclst, name, parameters, return_type, body) ->
    [ semantic_function generics environment (speclst, name, parameters, return_type, body) ]
  | _ -> toplevel_dfy generics statement

let prog_dfy p =
  reset ();
  (* Keep temporary/source-map state deterministic for callers that mix the
     compatibility conversion APIs with whole-program lowering. *)
  Convertcall.reset ();
  let p = Semantic.normalize_program p in
  let (n_p, gens) = Generics.prog p in
  let environment = Semantic.analyze n_p in
  let p = Convertfor.prog n_p in
  let (Program sl) = p in
  let d_funcs = List.fold ~f:(fun so_far s ->
    match s with
    | Function (speclst, name, parameters, return_type, body) when is_func s ->
      so_far @ [ semantic_function gens environment (speclst, name, parameters, return_type, body) ]
    | _ -> so_far) ~init:[] sl in
  let toplevel_stmts = List.filter ~f:(fun statement -> is_toplevel statement && not (is_func statement)) sl in
  let d_toplevel_stmts = List.fold ~f:(fun so_far s -> so_far@(semantic_toplevel gens environment s)) ~init:[] toplevel_stmts in
  let non_toplevel_stmts = List.filter ~f:(fun x -> not (is_toplevel x)) sl in
  let d_non_toplevel_stmts = Lowering.statements ~environment non_toplevel_stmts in
  let main = DMeth ([], (Lexing.dummy_pos, Some "Main"), [], [], [], Some d_non_toplevel_stmts) in
  DProg ("", d_funcs@d_toplevel_stmts@[main])
