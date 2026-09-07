open Base
open Pyparse.Sourcemap

exception ReportError of string
let[@inline] failwith msg = raise (ReportError msg)

let printf = Stdlib.Printf.printf
let prerr = Stdlib.prerr_string

let strip_ansi out =
  let length = String.length out in
  let buffer = Buffer.create length in
  let rec skip_escape index =
    if index >= length then index
    else if Char.is_alpha out.[index] then index + 1
    else skip_escape (index + 1)
  in
  let rec copy index =
    if index >= length then ()
    else if Char.equal out.[index] '\027' then copy (skip_escape (index + 1))
    else (
      Buffer.add_char buffer out.[index];
      copy (index + 1))
  in
  copy 0;
  Buffer.contents buffer

let replace_num ?(sourcemap = ref []) p =
  let nums = (Re2.find_all_exn (Re2.create_exn "[0-9]*") p) in
  let line_column = List.filter ~f:(fun s -> 
    let s = String.length s in if s = 0 then false else true) nums in
  let line = begin
    match (List.nth line_column 0) with
    | Some s -> Int.of_string s
    | None -> 0
    end in
  let column = begin
    match (List.nth line_column 1) with
    | Some s -> Int.of_string s
    | None -> 0
    end in
  let seg = Transform.Emitdfy.nearest_seg !sourcemap line column in
  let seg_str = print_seg seg in seg_str

let verification_errors ?(sourcemap = ref []) out =
  let out = strip_ansi out in
  try begin
    let line_rgx = Re2.create_exn "\\([0-9]*,[0-9]*\\).+" in
    let lines = Re2.find_all_exn line_rgx out in 
    let split_rgx = Re2.create_exn ":" in
    let split_f s = Re2.split split_rgx s in
    let split_lines = List.map ~f:split_f lines in
    let replaced_nums = List.map ~f:(fun lst -> List.mapi ~f:(fun i s -> if i = 0 then replace_num ~sourcemap s else s) lst) split_lines in
    let errors = List.map replaced_nums ~f:(fun l -> String.concat ~sep:", " l) in
    let errors_s = String.concat ~sep:"\n" errors in
    Some errors_s
  end with
  | Re2.Exceptions.Regex_match_failed _ -> None

let verification_summary out =
  let out = strip_ansi out in
  try begin
    let line_rgx = Re2.create_exn ("verifier finished with [0-9]+ verified, [0-9]+ error") in
    let line = (Re2.find_first_exn line_rgx out) ^ "(s)" in
    (* Runtime-library verification counts vary between Dafny releases. Keep
       the verifier's summary intact instead of subtracting a hard-coded
       number that silently becomes wrong after a library or tool upgrade. *)
    printf "%s\n" line
  end with
  | Re2.Exceptions.Regex_match_failed e -> failwith ("\nUnable to obtain verification summary due to regex match fail: " ^ e ^ "\n")

let report ?(sourcemap = ref []) out = begin match verification_errors ~sourcemap out with
  | Some s -> prerr (s ^ "\n")
  | None -> ()
  end;
  verification_summary out
