open Base

open Astdfy
open Pyparse.Sourcemap

let printf = Stdlib.Printf.printf

type line = int
[@@deriving sexp]
type column = int
[@@deriving sexp]

type sourcemap = ((line * column) * segment) list ref
[@@deriving sexp]

let sm: sourcemap = ref []
let add_sm k v s = sm := ((k, v), s)::!sm
let rec replicate_str s n = match n with
  | 0 -> ""
  | n -> let rest = replicate_str s (n - 1) in
    String.concat [s; rest]

let space = " "
let indent i = replicate_str space i
let curr_line : int ref = ref 1
let curr_column : int ref = ref 1
let newline = fun () -> (curr_column := 1; curr_line := !curr_line + 1; "\n")
let newline_f f = fun s -> let nf = (f s) in let nl = newline () in String.concat [nf; nl]
let newcolumn s = (curr_column := !curr_column + (String.length s); s)

let rec newline_concat f = function
  | [] -> ""
  | hd::[] -> f hd
  | hd::tl -> let fhd = f hd in
    let n = newline () in 
    let rest = newline_concat f tl in 
    String.concat [fhd; n; rest]

let rec newcolumn_concat f sep = function
  | [] -> ""
  | hd::[] -> f hd
  | hd::tl ->
    let fhd = f hd in 
    let n = newcolumn sep in
    let rest = newcolumn_concat f sep tl in
    String.concat [fhd; n; rest]

let ret_param_name = fun () -> "res" 

let curr_func : string ref = ref ""

type declarations = (string * string) list ref
let vars: declarations = ref []
let add_vars vl = List.iter vl ~f:(fun v -> vars := (!curr_func, seg_val v)::!vars)

(* All emitter state belongs to one translation. Reset it before every public
   emission so repeated test runs and library callers cannot observe stale
   line numbers, declarations, or source-map entries. *)
let reset () =
  sm := [];
  curr_line := 1;
  curr_column := 1;
  curr_func := "";
  vars := []

let rec lookup fn v = function
  | [] -> false
  | (f2, v2)::_ when (String.equal fn f2) && (String.equal v v2) -> true
  | _::tl -> lookup fn v tl


let newcolumn_h id s = 
  let nl = newline () in 
  let n = newcolumn (indent id) in 
  String.concat [nl; n; s]

(* if this is a temporary name, retrieve its name in the original source to store in the sourcemap *)
let source_from_temp name =
  match Base.Hashtbl.find Convertcall.temp_source name with 
  | Some v -> v
  | None -> name

let print_ident id seg =
  let n = newcolumn (indent id) in 
  let s = seg_val seg in
  let source_name = source_from_temp s in
  let n_seg = (fst seg, Some source_name) in
  add_sm !curr_line !curr_column n_seg;
  let ps = newcolumn s in
  String.concat [n; ps]

let add_op id seg v = 
  let n = newcolumn (indent id) in
  add_sm !curr_line !curr_column seg;
  let pv = newcolumn v in
  String.concat [n; pv]

let print_op id = function
  | DNotIn s -> add_op id s "!in"
  | DIn s -> add_op id s "in"
  | DPlus s -> add_op id s "+"
  | DMinus s -> add_op id s "-"
  | DTimes s -> add_op id s "*"
  | DDivide s -> add_op id s "/"
  | DMod s -> add_op id s "%"
  | DNEq s -> add_op id s "!="
  | DEq s -> add_op id s "=="
  | DLt s -> add_op id s "<"
  | DLEq s -> add_op id s "<="
  | DGt s -> add_op id s ">"
  | DGEq s -> add_op id s ">=" 
  | DAnd s -> add_op id s "&&" 
  | DOr s -> add_op id s "||"
  | DNot s -> add_op id s "!"
  | DBiImpl s -> add_op id s "<==>"
  | DImplies s -> add_op id s "==>"
  | DExplies s -> add_op id s "<=="

let rec type_parts t =
  match t with
  | DIdentTyp (s, gl) ->
    let name = seg_val s in
    let value = match gl with
      | [] -> name
      | _ -> name ^ "<" ^ String.concat ~sep:", " (List.map gl ~f:(fun t -> snd (type_parts t))) ^ ">"
    in s, value
  | DInt s -> s, "int"
  | DReal s -> s, "real"
  | DBool s -> s, "bool"
  | DString s -> s, "string"
  | DChar s -> s, "char"
  | DObj s -> s, "object"
  | DSeq (s, t) -> s, "seq<" ^ snd (type_parts t) ^ ">"
  | DSet (s, t) -> s, "set<" ^ snd (type_parts t) ^ ">"
  | DMap (s, t1, t2) ->
    s, "map<" ^ snd (type_parts t1) ^ ", " ^ snd (type_parts t2) ^ ">"
  | DArray (s, t) -> s, "array<" ^ snd (type_parts t) ^ ">"
  | DTuple (s, tl) ->
    s, "(" ^ String.concat ~sep:", " (List.map tl ~f:(fun t -> snd (type_parts t))) ^ ")"
  | DFunTyp (s, tl, t) ->
    let args = String.concat ~sep:", " (List.map tl ~f:(fun t -> snd (type_parts t))) in
    s, "(" ^ args ^ ") -> " ^ snd (type_parts t)
  | _ -> def_seg, ""

let print_type id t =
  let type_segment, type_value = type_parts t in
  add_op id type_segment type_value

let print_delimited id left right print_element elements =
  let n = newcolumn (indent id) in
  let opening = newcolumn left in
  let contents = newcolumn_concat print_element ", " elements in
  let closing = newcolumn right in
  String.concat [n; opening; contents; closing]

let print_expression_line id keyword terminator print_expression expression =
  let n = newcolumn (indent id) in
  let k = newcolumn keyword in
  let pe = print_expression expression in
  let t = newcolumn terminator in
  String.concat [n; k; pe; t]

(* (vars := (!curr_func, idd)::!vars); *)
let print_param id = function
  | (i, t) -> 
    let n = newcolumn (indent id) in 
    let idd = print_ident 0 i in 
    let pt = match t with 
    | DVoid -> "" 
    | _ -> let c = newcolumn ":" in let pt = print_type 1 t in String.concat [c; pt] in
    String.concat [n; idd; pt]

let rec print_exp id = function
  | DIdentifier s -> let n = newcolumn (indent id) in 
    let pid = print_ident 0 s in
    String.concat [n; pid]
  | DDot (e, ident) -> let n = newcolumn (indent id) in 
    let pe = print_exp 0 e in 
    let dot = newcolumn "." in
    let pid = print_ident 0 ident in
    String.concat [n; pe; dot; pid]
  | DBinary (e1, op, e2) -> let n = newcolumn (indent id) in 
    let ob = newcolumn "(" in 
    let pe1 = print_exp 0 e1 in
    let ps1 = newcolumn " " in
    let pop = print_op 0 op in
    let ps2 = newcolumn " " in 
    let pe2 = print_exp 0 e2 in
    let cb = newcolumn ")" in
    String.concat [n; ob; pe1; ps1; pop; ps2; pe2; cb]
  | DUnary (op, e) -> let n = newcolumn (indent id) in 
    let ob = newcolumn "(" in 
    let pop = (print_op 0 op) in 
    let pe = print_exp 0 e in 
    let cb = newcolumn ")" in
    String.concat [n; ob; pop; pe; cb]
  | DIntLit i -> let n = newcolumn (indent id) in 
    String.concat [n; i]
  | DRealLit r -> let n = newcolumn (indent id) in 
    String.concat [n; r]
  | DTrue -> let n = newcolumn (indent id) in 
    String.concat [n; "true"]
  | DFalse -> let n = newcolumn (indent id) in 
    String.concat [n; "false"]
  | DStringLit s -> let n = newcolumn (indent id) in 
    let es = "\"" ^ s ^ "\"" in
    String.concat [n; es]
  | DNull -> let n = newcolumn (indent id) in 
    let pn = newcolumn "null" in
    String.concat [n; pn]
  | DEmptyExpr -> newcolumn (indent id)
  | DThis -> let n = newcolumn (indent id) in 
    let pt = newcolumn "this" in
    String.concat [n; pt]
  | DCallExpr (e, el) -> let n = newcolumn (indent id) in 
    let pe = print_exp 0 e in 
    let ob = newcolumn "(" in 
    let pel = newcolumn_concat (print_exp 0) ", " el in 
    let cb = newcolumn ")" in
    String.concat [n; pe; ob; pel; cb]
  | DSeqExpr el -> print_delimited id "[" "]" (print_exp 0) el
  | DArrayExpr el -> print_delimited id "[" "]" (print_exp 0) el
  | DSetExpr el -> print_delimited id "{" "}" (print_exp 0) el
  | DMapExpr eel -> let n = newcolumn (indent id) in
    let m = newcolumn "map[" in
    let peel = newcolumn_concat (
      fun (k,v) -> 
        let pk = print_exp 0 k in 
        let c = newcolumn " := " in 
        let pv = print_exp 0 v in 
        String.concat [pk; c; pv]
      ) ", " eel in 
    let cb = (newcolumn "]") in 
    String.concat [n; m; peel; cb]
  | DSubscript (e1, e2) -> let n = newcolumn (indent id) in
    let pe1 = print_exp id e1 in 
    let pe2 = print_exp 0 e2 in
    String.concat [n; pe1; pe2]
  | DIndex e -> let n = newcolumn (indent id) in
    let pe = print_exp id e in 
    String.concat [n; pe]
  | DSlice (e1, e2) ->
    let n = newcolumn (indent id) in 
    let ob = (newcolumn "[") in
    let res = begin
      match e1, e2 with
      | Some r1, Some r2 -> let pe1 = (print_exp 0 r1) in 
        let pd = (newcolumn "..") in 
        let pe2 = (print_exp 0 r2) in
        String.concat [pe1; pd; pe2]
      | Some r1, None -> (print_exp 0 r1)
      | None, Some r2 -> (print_exp 0 r2)
      | None, None -> ""
    end
    in 
    let cb =  (newcolumn "]") in
    String.concat [n; ob; res; cb]
  | DForall (il, e) -> let n = newcolumn (indent id) in 
    let f = (newcolumn "forall ") in 
    let pil = (newcolumn_concat (print_ident 0) ", " il) in 
    let pd = (newcolumn " :: ") in
    let pe = (print_exp 0 e) in
    String.concat [n; f; pil; pd; pe]
  | DExists (il, e) -> let n = newcolumn (indent id) in
    let ex = (newcolumn "exists ") in
    let pil = (newcolumn_concat (print_ident 0) ", " il) in
    let pc = (newcolumn " :: ") in 
    let pe = (print_exp 0 e) in
    String.concat [n; ex; pil; pc; pe]
  | DLen (_, e) -> let n = newcolumn (indent id) in 
    let ob = newcolumn "|" in 
    let pe = print_exp 0 e in
    let cb = newcolumn "|" in
    String.concat [n; ob; pe; cb]
  | DOld (_, e) -> let n = newcolumn (indent id) in 
    let old = newcolumn "old(" in 
    let pe = print_exp 0 e in
    let cb = newcolumn ")" in
    String.concat [n; old; pe; cb]
  | DFresh (_, e) -> let n = newcolumn (indent id) in 
    let fresh = newcolumn "fresh(" in 
    let pe = print_exp 0 e in
    let cb = newcolumn ")" in
    String.concat [n; fresh; pe; cb]
  | DLambda (fl, sl, e) -> let n = newcolumn (indent id) in
    let ob = newcolumn "(" in
    let pfl = newcolumn_concat (print_param 0) ", " fl in
    let cb = newcolumn ")" in
    let psl = newcolumn_concat (print_spec 0) ", " sl in
    let op = newcolumn " =>" in
    let pe = print_exp 1 e in
    String.concat [n; ob; pfl; cb; psl; op; pe]
  | DIfElseExpr (c, e1, e2) -> let n = newcolumn (indent id) in
    let i = newcolumn "if " in
    let pc = print_exp 0 c in
    let t = newcolumn " then" in
    let pe1 = print_exp 1 e1 in
    let el = newcolumn " else" in
    let pe2 = print_exp 1 e2 in
    String.concat [n; i; pc; t; pe1; el; pe2]
  | DTupleExpr el -> print_delimited id "(" ")" (print_exp 0) el

and print_spec id = function
  | DRequires e -> print_expression_line id "requires" "" (print_exp 1) e
  | DEnsures e -> print_expression_line id "ensures" "" (print_exp 1) e
  | DInvariant e -> print_expression_line id "invariant" "" (print_exp 1) e
  | DDecreases e -> print_expression_line id "decreases" "" (print_exp 1) e
  | DReads e -> print_expression_line id "reads" "" (print_exp 1) e
  | DModifies e -> print_expression_line id "modifies" "" (print_exp 1) e

let print_rhs print_expression = function
  | [] -> ""
  | expressions ->
    let assignment = newcolumn " := " in
    let values = newcolumn_concat print_expression ", " expressions in
    String.concat [assignment; values]

let rec print_rets id = function
  | [] -> ""
  | DVoid::_ -> ""
  | tl -> let n = newcolumn (indent id) in 
    let r = newcolumn "(" in 
    let ptl = newcolumn_concat (
        fun x -> 
          let name = newcolumn (ret_param_name ()) in 
          let ps = newcolumn ":" in 
          let pt = print_type 1 x in 
          String.concat [name; ps; pt]
      ) ", " tl in 
    let cb = (newcolumn ")") in
    String.concat[n; r; ptl; cb]

and print_stmt id = function
  | DEmptyStmt -> ""
  | DAssume e -> print_expression_line id "assume" ";" (print_exp 1) e
  | DAssert e -> print_expression_line id "assert" ";" (print_exp 1) e
  | DBreak -> let n = newcolumn (indent id) in 
    let b = newcolumn "break" in 
    let ps = (newcolumn ";") in
    String.concat [n; b; ps]
  | DAssign (_, [], _) -> ""
  | DAssign (None, first::rest, el) -> let n = newcolumn (indent id) in
    let exists = (lookup (!curr_func) (seg_val first) !vars) in
    let pre = match exists with
      | true -> ""
      | false -> add_vars (first::rest); newcolumn "var " in
    let pil = newcolumn_concat (print_ident 0) ", " (first::rest) in
    let pt = "" in
    let prhs = print_rhs (print_exp 0) el in
    let ps = newcolumn ";" in 
    String.concat [n; pre; pil; pt; prhs; ps]
  | DAssign (Some tp, il, el) -> let n = newcolumn (indent id) in
    let pre = add_vars il; newcolumn "var " in
    let pil = newcolumn_concat (print_ident 0) ", " il in
    let pt = 
      let c = newcolumn ":" in let pt = print_type 1 tp in String.concat [c; pt]
    in
    let prhs = print_rhs (print_exp 0) el in
    let ps = newcolumn ";" in 
    String.concat [n; pre; pil; pt; prhs; ps]
  | DCallStmt (e, el) -> let n = newcolumn (indent id) in 
    let pident = print_exp 0 e in 
    let ob = newcolumn "(" in 
    let pel = newcolumn_concat (print_exp 0) ", " el in
    let cb = newcolumn ")" in 
    let ps = newcolumn ";" in
    String.concat [n; pident; ob; pel; cb; ps]
  | DIf (e, sl1, sl2, sl3) -> let n = newcolumn (indent id) in
    let i = newcolumn "if " in 
    let pe = print_exp 0 e in
    let ob = newcolumn " {" in 
    let nl = newline () in
    let pst = newline_concat (print_stmt (id+2)) sl1 in
    let nl2 = newline () in
    let n2 = newcolumn (indent id) in
    let cb = newcolumn "}" in 
    let pelif = match sl2 with
      | [] -> ""
      | _ -> begin
      let res (e, sl) = begin
        let pel = newcolumn " else if" in
        let pe = print_exp 1 e in
        let ob = newcolumn " {" in
        let nl = newline () in 
        let pst = newline_concat (print_stmt (id+2)) sl in
        let nl2 = newline () in 
        let n = newcolumn (indent id) in
        let cb = newcolumn "}" in
        String.concat [pel; pe; ob; nl; pst; nl2; n; cb]
      end in
      newcolumn_concat res "" sl2
    end in
    let pelse = match sl3 with
      | [] -> ""
      | _ -> begin
      let pecb = newcolumn " else {" in 
      let nl = newline () in 
      let pst = newline_concat (print_stmt (id+2)) sl3 in
      let n = newcolumn (indent id) in 
      let nl2 = newline () in
      let n2 = newcolumn (indent id) in
      let cb = newcolumn "}" in
      String.concat [pecb; nl; pst; n; nl2; n2; cb]
    end in
    String.concat [n; i; pe; ob; nl; pst; nl2; n2; cb; pelif; pelse]
  | DWhile (speclst, e, sl) -> let n = newcolumn (indent id) in
    let w = newcolumn "while " in
    let pe = print_exp 0 e in
    let nl = newline () in 
    let psl = newline_concat (print_spec (id+2)) speclst in
    let ob = (newcolumn_h id "{") in 
    let nl2 = newline () in
    let pst = newline_concat (print_stmt (id+2)) sl in
    let nl3 = newline () in 
    let n2 = newcolumn (indent id) in
    let cb = newcolumn "}" in
    String.concat [n; w; pe; nl; psl; ob; nl2; pst; nl3; n2; cb]
  | DReturn el -> let n = newcolumn (indent id) in
    let r = newcolumn "return " in 
    let pel = (newcolumn_concat (print_exp 0) ", " el) in 
    let ps = newcolumn ";" in
    String.concat [n; r; pel; ps]

let print_declaration id = function
  | (i, t) -> print_stmt id (DAssign (Some t, [i], [DIdentifier i]))

let print_toplevel id = function
  | DMeth (speclst, ident, gl, pl, tl, osl) -> (curr_func := seg_val ident); 
    let n = newcolumn (indent id) in 
    let m = newcolumn "method" in
    let pident = print_ident 1 ident in
    let pgl = match gl with | [] -> "" | gl -> begin
      let ob = newcolumn "<" in
      let pvs = newcolumn_concat (fun s -> s) ", " gl in
      let cb = newcolumn ">" in
      String.concat [ob; pvs; cb]
    end in
    let ob = newcolumn "(" in    
    let pp = newcolumn_concat (print_param 0) ", " pl in
    let cb = newcolumn ")" in
    let pr = begin match tl with | [] -> "" | DVoid::_ -> "" 
      | tl -> let rt = newcolumn " returns" in let pp = print_rets 1 tl in
      String.concat [rt; pp]
    end in
    let nl = newline () in
    let pspeclst = newline_concat (print_spec (id+2)) speclst in
    let nl2 = newline () in
    let n2 = newcolumn (indent id) in
    let psl = match osl with None -> "" | Some sl ->
      let ob2 = newcolumn "{" in
      let nl3 = newline () in
      let ppl = newline_concat (print_declaration (id+2)) pl in 
      let nl4 = newline () in
      let pst = newcolumn_concat (fun x -> newline_f (print_stmt (id+2)) x) "" sl in
      let n3 = newcolumn (indent id) in
      let cb2 = newcolumn "}" in
      let nl5 = newline () in 
      String.concat [ob2; nl3; ppl; nl4; pst; n3; cb2; nl5]
    in String.concat [
      n; m; pident; pgl; ob; pp; cb; pr; nl; pspeclst; nl2; n2; psl
    ]
  | DFuncMeth (speclst, ident, gl, pl, t, oe) -> (curr_func := seg_val ident);
    let n = newcolumn (indent id) in 
    let m = newcolumn "function" in
    let pident = print_ident 1 ident in
    let pgl = match gl with | [] -> "" | gl -> begin
      let ob = newcolumn "<" in
      let pvs = newcolumn_concat (fun s -> s) ", " gl in
      let cb = newcolumn ">" in
      String.concat [ob; pvs; cb]
    end in
    let ob = newcolumn "(" in    
    let pp = newcolumn_concat (print_param 0) ", " pl in
    let cb = newcolumn ")" in
    let pr = begin
      match t with | DVoid -> "" 
      | t -> let c = newcolumn ":" in let pp = print_rets 1 [t] in
      String.concat [c; pp]
    end in
    let nl = newline () in
    let psl = newline_concat (print_spec (id+2)) speclst in
    let nl2 = newline () in
    let pe = match oe with None -> "" | Some e ->
      let n2 = newcolumn (indent id) in
      let ob2 = newcolumn "{" in
      let nl3 = newline () in
      let n3 = newcolumn (indent (id+2)) in
      let pe = print_exp 0 e in
      let nl4 = newline () in
      let n4 = newcolumn (indent id) in
      let cb2 = newcolumn "}" in 
      let nl5 = newline () in 
      String.concat [n2; ob2; nl3; n3; pe; nl4; n4; cb2; nl5]
    in 
    String.concat [n; m; pident; pgl; ob; pp; cb; pr; nl; psl; nl2; pe]

  | DTypSynonym (ident, otyp) -> let n = newcolumn (indent id) in
    let t = newcolumn "type" in
    let pident = print_ident 1 ident in
    let pet = match otyp with | None -> "" 
      | Some typ -> let eq = newcolumn " = " in let pt = print_type 0 typ in
      String.concat [eq; pt] in
    String.concat [n; t; pident; pet] 

let print_prog program =
  reset ();
  match program with
  | DProg(_, tll) -> newcolumn_concat (fun x -> newline_f (print_toplevel 0) x) "" tll

let print_prog_with_sourcemap program =
  let source = print_prog program in
  let source_map = ref (List.map !sm ~f:(fun mapping -> mapping)) in
  source, source_map

let nearest_candidate line column mapping nearest =
  let ldiff = Int.abs ((fst (fst mapping)) - line) in
  let l_so_far = Int.abs ((fst (fst nearest)) - line) in
  match Int.compare ldiff l_so_far with
  | -1 -> mapping
  | 0 ->
    let cdiff = Int.abs ((snd (fst mapping)) - column) in
    let c_so_far = Int.abs ((snd (fst nearest)) - column) in
    (match Int.compare cdiff c_so_far with
     | -1 -> mapping
     | _ -> nearest)
  | _ -> nearest

let rec nearest_seg_helper sm line column nearest = 
  match List.hd sm with
  | Some mapping -> 
    let rest = List.tl_exn sm in
    nearest_seg_helper rest line column (nearest_candidate line column mapping nearest)
  | None -> nearest

(* finds the nearest dafny segment, then returns its corresponding python segment *)
let nearest_seg sm line column = 
    let res = nearest_seg_helper sm line column ((Int.max_value, Int.max_value), def_seg) in
    snd res

let print_pos p = String.concat ["("; (Int.to_string (fst p)); ", "; (Int.to_string (snd p)); "): "]
let print_sourcemap sm = String.concat ~sep:"\n" (List.map ~f:(fun e -> String.concat [(print_pos (fst e)); " "; (print_seg (snd e))]) sm)
