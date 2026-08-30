open Alcotest

module Ast = Pyparse.Astpy
module D = Transform.Astdfy
open Pyparse.Sourcemap

let parse_program source =
  match Pyparse.Parser.parse_string source with
  | Ast.Program statements -> statements

let has_substring source pattern =
  let source_length = String.length source in
  let pattern_length = String.length pattern in
  let rec search index =
    if index + pattern_length > source_length then false
    else if String.sub source index pattern_length = pattern then true
    else search (index + 1)
  in
  pattern_length = 0 || search 0

let test_dafny4_function_syntax () =
  let ast = Transform.Todafnyast.prog_dfy (Ast.Program (parse_program "def f(x: int) -> int:\n  return x\n")) in
  let generated, _ = Transform.Emitdfy.print_prog_with_sourcemap ast in
  check bool "Dafny 4 function syntax is emitted" true (has_substring generated "function f(");
  check bool "legacy function syntax is not emitted" false (has_substring generated "function method")

let test_parser_assignment () =
  match parse_program "x: int = 1\n" with
  | [ Ast.Assign (Some (Ast.Typ (Ast.TInt _)), [ Ast.Identifier (_, Some "x") ], [ Ast.Literal (Ast.IntLit "1") ]) ] -> ()
  | _ -> fail "the typed assignment AST did not match"

let test_parser_specs_and_control_flow () =
  match parse_program "# pre x >= 0\ndef f(x: int) -> int:\n  # invariant x >= 0\n  while x > 0:\n    x -= 1\n" with
  | [ Ast.Function ([ Ast.Pre _ ], _, _, _, [ Ast.While ([ Ast.Invariant _ ], _, _) ]) ] -> ()
  | _ -> fail "specification or control-flow parsing did not match"

let test_parser_fresh () =
  match parse_program "assert fresh(x)\n" with
  | [ Ast.Assert (Ast.Fresh _) ] -> ()
  | _ -> fail "fresh was not parsed as a Fresh expression"

let test_transform_state_resets () =
  let input = parse_program "x = f(1)\n" in
  Transform.Convertcall.reset ();
  ignore
    (Transform.Convertcall.exp_calls
       (Ast.Call (Ast.Identifier (Pyparse.Sourcemap.new_seg 1 1 (Some "f")), [])));
  check string "temporary source is recorded" "f"
    (Transform.Emitdfy.source_from_temp "tempcall_1");
  Transform.Convertcall.reset ();
  check string "temporary source is cleared" "tempcall_1"
    (Transform.Emitdfy.source_from_temp "tempcall_1");
  let first = Transform.Convertcall.prog (Ast.Program input) in
  let second = Transform.Convertcall.prog (Ast.Program input) in
  let first_name =
    match first with
    | Ast.Program (Ast.Assign (_, [ Ast.Identifier (_, Some name) ], _) :: _) -> name
    | _ -> fail "call conversion did not create a temporary assignment"
  in
  let second_name =
    match second with
    | Ast.Program (Ast.Assign (_, [ Ast.Identifier (_, Some name) ], _) :: _) -> name
    | _ -> fail "call conversion did not create a second temporary assignment"
  in
  check string "temporary names are per-run" first_name second_name

let test_pipeline_injects_commands_and_cleans_files () =
  let root = Filename.temp_file "dafny-of-python-test-" ".tmp" in
  Sys.remove root;
  Unix.mkdir root 0o700;
  let commands = ref [] in
  let runner (command : Run.Pipeline.command) =
    commands := command :: !commands;
    if String.equal command.program "mypy" then
      ({ exit_code = 0; stdout = "success"; stderr = "" } : Run.Pipeline.command_result)
    else
      ({ exit_code = 0
      ; stdout = "verifier finished with 1 verified, 0 errors\n"
      ; stderr = ""
      } : Run.Pipeline.command_result)
  in
  let base = Run.Pipeline.default_config ~prelude:"prelude.dfy" ~list_library:"list.dfy" in
  let config = { base with temp_root = Some root; runner } in
  let result = Run.Pipeline.run ~config "x = 1\n" in
  check bool "artifacts are cleaned by default" false (Option.is_some result.working_directory);
  check int "both external commands were called" 2 (List.length !commands);
  check bool "generated Dafny is non-empty" true (String.length result.dafny_source > 0);
  check bool "temporary root is empty" true (Array.length (Sys.readdir root) = 0);
  Unix.rmdir root

let test_emitter_resets_state () =
  let ast = Transform.Todafnyast.prog_dfy (Ast.Program [ Ast.Assign (None, [ Ast.Identifier (Pyparse.Sourcemap.def_pos, Some "x") ], [ Ast.Literal (Ast.IntLit "1") ]) ]) in
  let first, first_map = Transform.Emitdfy.print_prog_with_sourcemap ast in
  let second, second_map = Transform.Emitdfy.print_prog_with_sourcemap ast in
  check string "repeated emission is stable" first second;
  check int "repeated emission has same map size" (List.length !first_map) (List.length !second_map)

let segment ?(line = 1) ?(column = 1) name =
  Pyparse.Sourcemap.new_seg line column (Some name)

let identifier ?line ?column name = Ast.Identifier (segment ?line ?column name)

module Raw_parser_for_test = struct
  type token = string
  type result = string
  exception LexError of string
  exception ParseError

  type mode = Ok | Lex | Parse
  let mode = ref Ok

  let next_token _ = "next"
  let indent _ = "indent"
  let parse next lexbuf =
    let token = next lexbuf in
    match !mode with
    | Ok -> token
    | Lex -> raise (LexError "bad token")
    | Parse -> raise ParseError
end

module Nice_parser_for_test = Pyparse.Nice_parser.Make (Raw_parser_for_test)

let parse_file_round_trip () =
  let path = Filename.temp_file "dafny-of-python-parser-" ".py" in
  Fun.protect
    ~finally:(fun () -> if Sys.file_exists path then Sys.remove path)
    (fun () ->
       Stdio.Out_channel.write_all path ~data:"x = 1\n";
       match Pyparse.Parser.parse_file path with
       | Ast.Program (Ast.Assign _ :: _) -> ()
       | _ -> fail "parse_file did not parse an assignment")

let test_parser_entry_points_and_errors () =
  let source =
    "# pre x >= 0\n"
    ^ "def f(x: int, ys: list[int]) -> int:\n"
    ^ "  # invariant x >= 0\n"
    ^ "  while x > 0:\n"
    ^ "    x -= 1\n"
  in
  let parsed = Pyparse.Parser.parse_string source in
  (match parsed with
   | Ast.Program [ Ast.Function (specs, _, params, _, [ Ast.While (loop_specs, _, _) ]) ] ->
     check int "all function specifications" 1 (List.length specs);
     check int "all parameters" 2 (List.length params);
     check int "loop specification" 1 (List.length loop_specs)
   | _ -> fail "the parser did not preserve nested specifications and control flow");
  (match Pyparse.Parser.parse_string "import typing\nfrom typing import TypeVar\nx = 1\n" with
   | Ast.Program [ Ast.Assign _ ] -> ()
   | _ -> fail "imports and comments should be ignored");
  List.iter
    (fun keyword ->
       let source = "# " ^ keyword ^ " x\ndef f(x: int) -> int:\n  pass\n" in
       match Pyparse.Parser.parse_string source with
       | Ast.Program [ Ast.Function ([ _ ], _, _, _, [ Ast.Pass ]) ] -> ()
       | _ -> fail (keyword ^ " specification was not parsed"))
    [ "post"; "decreases"; "reads"; "modifies" ];
  (match Pyparse.Parser.parse_string "x = 1\n\ny = 2; z = 3\n" with
   | Ast.Program [ Ast.Assign _; Ast.Assign _; Ast.Assign _ ] -> ()
   | _ -> fail "blank lines and semicolons should be accepted");
  parse_file_round_trip ();
  let source_position =
    { Lexing.dummy_pos with pos_fname = "input.py"; pos_lnum = 7; pos_cnum = 3 }
  in
  ignore (Pyparse.Parser.parse_string ~pos:source_position "x = 1\n");
  let parse_channel = Filename.temp_file "dafny-of-python-parser-" ".py" in
  Fun.protect
    ~finally:(fun () -> if Sys.file_exists parse_channel then Sys.remove parse_channel)
    (fun () ->
       Stdio.Out_channel.write_all parse_channel ~data:"x = 1\n";
       In_channel.with_open_bin parse_channel (fun input ->
         ignore (Pyparse.Parser.parse_chan input)));
  (try
     ignore (Pyparse.Parser.parse_string "x = @\n");
     fail "an illegal character should raise Parser.LexError"
   with
   | Pyparse.Parser.LexError _ -> ());
  (try
     ignore (Pyparse.Parser.parse_string "def broken(:\n");
     fail "malformed syntax should raise Parser.ParseError"
   with
     | Pyparse.Parser.ParseError _ -> ());
  let lexbuf = Lexing.from_string "\n  x" in
  let token () = Pyparse.Indenter.f lexbuf in
  (match token (), token (), token (), token (), token (), token () with
   | Pyparse.Menhir_parser.NEWLINE,
     Pyparse.Menhir_parser.INDENT,
     Pyparse.Menhir_parser.IDENTIFIER _,
     Pyparse.Menhir_parser.NEWLINE,
     Pyparse.Menhir_parser.DEDENT,
     Pyparse.Menhir_parser.EOF -> ()
   | _ -> fail "indenter should flush dedents before EOF");
  (match token () with
   | Pyparse.Menhir_parser.EOF -> ()
   | _ -> fail "indenter should remain at EOF after flushing dedents")

let test_nice_parser_wrapper_paths () =
  let module P = Nice_parser_for_test in
  let expect name predicate f =
    try
      ignore (f ());
      fail (name ^ " should raise")
    with
    | exn when predicate exn -> ()
    | exn -> fail (name ^ " raised " ^ Printexc.to_string exn)
  in
  P.pp_exceptions ();
  (match Location.error_of_exn (P.LexError { msg = "bad"; loc = Location.none }) with
   | Some (`Ok _) -> ()
   | _ -> fail "LexError should be rendered by the location printer");
  (match Location.error_of_exn (P.ParseError { token = "token"; loc = Location.none }) with
   | Some (`Ok _) -> ()
   | _ -> fail "ParseError should be rendered by the location printer");
  let rendered = Printexc.to_string (P.LexError { msg = "bad"; loc = Location.none }) in
  check bool "registered exception printer renders errors" true
    (String.length rendered > 0);
  ignore (Printexc.to_string (Failure "ordinary"));
  Raw_parser_for_test.mode := Ok;
  Location.input_lexbuf := None;
  check string "raw parser result" "indent" (P.parse_string "input");
  check bool "parser records its input lexbuf" true
    (Option.is_some !Location.input_lexbuf);
  let position = { Lexing.dummy_pos with pos_fname = "position.py"; pos_lnum = 3 } in
  ignore (P.parse_string ~pos:position "input");
  let channel_path = Filename.temp_file "dafny-of-python-nice-parser-" ".txt" in
  Fun.protect
    ~finally:(fun () -> if Sys.file_exists channel_path then Sys.remove channel_path)
    (fun () ->
       Stdio.Out_channel.write_all channel_path ~data:"input";
       In_channel.with_open_bin channel_path (fun channel ->
         check string "channel parser result" "indent" (P.parse_chan channel));
       In_channel.with_open_bin channel_path (fun channel ->
         ignore (P.parse_chan ~pos:position channel));
       check string "file parser result" "indent" (P.parse_file channel_path));
  Raw_parser_for_test.mode := Lex;
  expect "wrapped lexical error" (function P.LexError _ -> true | _ -> false)
    (fun () -> P.parse_string "input");
  Raw_parser_for_test.mode := Parse;
  expect "wrapped parse error" (function P.ParseError _ -> true | _ -> false)
    (fun () -> P.parse_string "input");
  Raw_parser_for_test.mode := Ok

let test_parser_expression_and_type_forms () =
  let forms =
    [ "list", "a = [1, 2]\n"
    ; "set", "b = {1, 2}\n"
    ; "dict", "c = {1: 2}\n"
    ; "tuple", "d = (1, 2)\n"
    ; "index", "e = a[1]\n"
    ; "range slice", "f = a[1:2]\n"
    ; "lower slice", "g = a[1:]\n"
    ; "upper slice", "h = a[:2]\n"
    ; "full slice", "i = a[:]\n"
    ; "old", "j = old(a)\n"
    ; "fresh", "k = fresh(a)\n"
    ; "max", "m = max(a)\n"
    ; "forall", "n = forall x, y :: x < y\n"
    ; "exists", "o = exists x :: x == 0\n"
    ; "lambda", "p = lambda x, y: x + y\n"
    ; "conditional", "q = 1 if True else 2\n"
    ; "not", "r = not False\n"
    ; "float", "s = -1.5e+2\n"
    ; "string", "t = \"ab\"\n"
    ; "not in", "u = a not in b\n"
    ; "in", "v = a in b\n"
    ; "bi-implication", "w = a <==> b\n"
    ; "implication", "x = a ==> b\n"
    ; "reverse implication", "y = a <== b\n"
    ; "minus", "z = a - b\n"
    ; "times", "aa = a * b\n"
    ; "divide", "ab = a / b\n"
    ; "mod", "ac = a % b\n"
    ; "not equal", "ad = a != b\n"
    ; "less equal", "ae = a <= b\n"
    ; "greater", "af = a > b\n"
    ; "greater equal", "ag = a >= b\n"
    ; "and", "ah = a and b\n"
    ; "or", "ai = a or b\n"
    ; "typed call", "aj = int(1)\n"
    ]
  in
  List.iter
    (fun (name, source) ->
       try ignore (Pyparse.Parser.parse_string source) with
       | exn -> failf "%s form did not parse: %s" name (Printexc.to_string exn))
    forms;
  (match Pyparse.Parser.parse_string "k = fresh(a)\n" with
   | Ast.Program [ Ast.Assign (_, _, [ Ast.Fresh _ ]) ] -> ()
   | _ -> fail "fresh expression was not parsed");
  (match Pyparse.Parser.parse_string "m = max(a)\n" with
   | Ast.Program [ Ast.Assign (_, _, [ Ast.Max _ ]) ] -> ()
   | _ -> fail "max expression was not parsed");
  (match Pyparse.Parser.parse_string "x: list[int] = [1]\n" with
   | Ast.Program [ Ast.Assign (Some (Ast.Typ (Ast.TLst (_, Some (Ast.TInt _)))), _, _) ] -> ()
   | _ -> fail "parameterized list type was not parsed");
  (match Pyparse.Parser.parse_string
           "def f(a: float, b: bool, c: str, d: object, e: dict[str, int], f: set[int], g: tuple[int, str], h: Callable[[int], str], i: Type[int]) -> None:\n  pass\n" with
   | Ast.Program [ Ast.Function (_, _, params, Ast.Typ (Ast.TNone _), [ Ast.Pass ]) ] ->
     check int "all parameterized types" 9 (List.length params)
   | _ -> fail "the type grammar did not preserve parameterized types")

let test_ast_utilities () =
  let open Ast in
  let int_type = TInt Pyparse.Sourcemap.def_seg in
  let float_type = TFloat Pyparse.Sourcemap.def_seg in
  let list_int = TLst (Pyparse.Sourcemap.def_seg, Some int_type) in
  let list_any = TLst (Pyparse.Sourcemap.def_seg, None) in
  check bool "integer subtype" true (subtyp int_type int_type);
  check bool "integer promotes to float" true (subtyp int_type float_type);
  check bool "float does not promote to integer" false (subtyp float_type int_type);
  check bool "list subtype" true (subtyp list_int list_any);
  check bool "list mismatch" false (subtyp list_int (TLst (def_seg, Some (TStr def_seg))));
  check bool "optional mismatch" false (subtyp list_any list_int);
  check bool "tuple subtype" true
    (subtyp (TTuple (def_seg, Some [ int_type; float_type ]))
       (TTuple (def_seg, Some [ int_type; float_type ])));
  check bool "tuple length mismatch" false
    (subtyp (TTuple (def_seg, Some [ int_type ])) (TTuple (def_seg, Some [])));
  check bool "dict subtype" true
    (subtyp (TDict (def_seg, Some int_type, Some float_type))
       (TDict (def_seg, Some int_type, Some float_type)));
  check bool "set subtype" true
    (subtyp (TSet (def_seg, Some int_type)) (TSet (def_seg, Some int_type)));
  check bool "equal types" true (eqtyp int_type int_type);
  check bool "either subtype" true (either_subtyp int_type float_type);
  check string "segment value" "value" (seg_val (segment "value"));
  check string "segment without value" "" (seg_val def_seg);
  check string "position" "Line: 2  Column: 3" (print_pos (fst (new_seg 2 3 None)));
  let positioned = { pos_fname = ""; pos_lnum = 2; pos_bol = 5; pos_cnum = 8 } in
  check string "position column uses line offset" "Line: 2  Column: 3"
    (print_pos positioned);
  check string "segment update" "new" (seg_val (update_seg_val (segment "old") (Some "new")));
  check int "segment values compare" 0 (seg_val_compare (segment "same") (segment "same"));
  ignore (seg_pos (segment "position"));
  ignore (sexp_of_pos (fst (segment "position")));
  ignore (sexp_of_segment (segment "position"));
  ignore (sexp_of_linecol (2, 3));
  ignore (sexp_of_sourcemap (ref [ ((2, 3), segment "position") ]));
  (try
     ignore (idlst_to_id [ Literal (IntLit "1") ]);
     fail "invalid identifier lists should raise"
   with
   | Pyparse.Astpy.PyAstError _ -> ())

let test_ast_serializers_and_subtyping () =
  let open Ast in
  let s = def_seg in
  let primitive_types =
    [ TIdent s; TInt s; TFloat s; TBool s; TStr s; TNone s; TObj s ]
  in
  let all_types =
    primitive_types
    @ [ TLst (s, Some (TInt s)); TLst (s, None)
      ; TDict (s, Some (TInt s), Some (TStr s)); TDict (s, None, Some (TStr s))
      ; TSet (s, Some (TInt s)); TTuple (s, Some primitive_types); TTuple (s, None)
      ; TCallable (s, primitive_types, TInt s); TType (s, Some (TInt s))
      ]
  in
  List.iter (fun typ -> ignore (sexp_of_typ typ)) all_types;
  List.iter (fun value -> ignore (sexp_of_unaryop value)) [ Not s; UMinus s ];
  List.iter
    (fun value -> ignore (sexp_of_literal value))
    [ TrueLit; FalseLit; IntLit "1"; FloatLit "1.0"; StringLit "s"; NoneLit ];
  let operators =
    [ Plus s; Minus s; Times s; Divide s; Mod s; EqEq s; NEq s; Lt s; LEq s
    ; Gt s; GEq s; And s; Or s; NotIn s; In s; BiImpl s; Implies s; Explies s ]
  in
  List.iter (fun value -> ignore (sexp_of_binaryop value)) operators;
  let x = Identifier s in
  let expressions =
    [ Typ (TInt s); Literal TrueLit; x; Dot (x, s); BinaryExp (x, Plus s, x)
    ; UnaryExp (Not s, x); Call (x, [ x ]); Lst [ x ]; Array [ x ]; Set [ x ]
    ; Dict [ (x, x) ]; Tuple [ x ]; Subscript (x, x); Index x
    ; Slice (Some x, Some x); Forall ([ s ], x); Exists ([ s ], x)
    ; Len (s, x); Max (s, x); Old (s, x); Fresh (s, x); Lambda ([ s ], x)
    ; IfElseExp (x, x, x); Slice (Some x, None); Slice (None, Some x)
    ; Slice (None, None)
    ]
  in
  List.iter (fun value -> ignore (sexp_of_exp value)) expressions;
  List.iter (fun value -> ignore (sexp_of_identifier value)) [ s ];
  List.iter (fun value -> ignore (sexp_of_param value)) [ (s, x) ];
  List.iter
    (fun value -> ignore (sexp_of_spec value))
    [ Pre x; Post x; Invariant x; Decreases x; Reads x; Modifies x ];
  let statements =
    [ IfElse (x, [ Pass ], [ (x, [ Break ]) ], [ Continue ])
    ; For ([], [ s ], x, [ Pass ]); While ([], x, [ Pass ])
    ; Assign (Some (Typ (TInt s)), [ x ], [ x ]); Function ([], s, [ (s, x) ], x, [ Pass ])
    ; Return x; Assert x; Break; Continue; Pass; Exp x
    ]
  in
  List.iter (fun value -> ignore (sexp_of_stmt value)) statements;
  ignore (sexp_of_program (Program statements));
  check bool "identical primitive types are subtypes" true (subtyp (TBool s) (TBool s));
  check bool "different primitive types are not subtypes" false (subtyp (TBool s) (TStr s));
  check bool "identifiers are not concrete subtypes" false (subtyp (TIdent s) (TIdent s));
  check bool "untyped lists compare as equal" true (eqtyp (TLst (s, None)) (TLst (s, None)));
  check bool "typed list elements compare recursively" true
    (subtyp (TLst (s, Some (TInt s))) (TLst (s, Some (TInt s))));
  check bool "untyped dictionaries compare as equal" true
    (eqtyp (TDict (s, None, None)) (TDict (s, None, None)));
  check bool "tuple None option compares as equal" true
    (eqtyp (TTuple (s, None)) (TTuple (s, None)));
  check bool "tuple option mismatch" false
    (subtyp (TTuple (s, Some [ TInt s ])) (TTuple (s, None)));
  check bool "tuple element mismatch" false
    (subtyp (TTuple (s, Some [ TFloat s ])) (TTuple (s, Some [ TInt s ])));
  check bool "set option mismatch" false
    (subtyp (TSet (s, Some (TInt s))) (TSet (s, None)));
  check bool "string types are subtypes" true (subtyp (TStr s) (TStr s));
  check bool "none types are subtypes" true (subtyp (TNone s) (TNone s));
  check bool "untyped tuple mismatch" false
    (subtyp (TTuple (s, None)) (TTuple (s, Some [ TInt s ])))

let expect_exception name predicate f =
  try
    ignore (f ());
    fail (name ^ " should raise")
  with
  | exn when predicate exn -> ()
  | exn -> fail (name ^ " raised " ^ Printexc.to_string exn)

let test_convertlist_paths () =
  let open Ast in
  let xs = identifier "xs" in
  let list = Lst [ Literal (IntLit "1"); Literal (IntLit "2") ] in
  let slices =
    [ Slice (Some (Literal (IntLit "1")), Some (Literal (IntLit "2")))
    ; Slice (Some (Literal (IntLit "1")), None)
    ; Slice (None, Some (Literal (IntLit "2")))
    ; Slice (None, None)
    ; Index (Literal (IntLit "0"))
    ]
  in
  let slice_assignments =
    List.map
      (fun slice -> Assign (None, [ identifier "out" ], [ Subscript (xs, slice) ]))
      slices
  in
  let converted =
    Transform.Convertlist.prog
      (Program (Assign (None, [ identifier "value" ], [ list ]) :: slice_assignments
                @ [ Assign (None, [ identifier "size" ], [ Len (def_seg, xs) ])
                  ; Exp (Array [ Literal (IntLit "3") ]) ]))
  in
  (match converted with
   | Program (Assign (_, [ Identifier (_, Some "templist_1") ], _) :: _) -> ()
   | _ -> fail "list literals should become runtime list construction");
  let has_method method_name = function
    | Assign (_, _, [ Call (Dot (_, (_, Some name)), _) ]) -> String.equal name method_name
    | _ -> false
  in
  (match converted with
   | Program statements ->
     check bool "range slice" true (List.exists (has_method "range") statements);
     check bool "lower slice" true (List.exists (has_method "rangeLower") statements);
     check bool "upper slice" true (List.exists (has_method "rangeUpper") statements);
     check bool "full slice" true (List.exists (has_method "rangeNone") statements);
     check bool "index" true (List.exists (has_method "atIndex") statements);
     check bool "length" true (List.exists (has_method "len") statements);
     check bool "array preserved" true
       (List.exists
          (function Exp (Array [ Literal (IntLit "3") ]) -> true | _ -> false)
          statements));
  List.iter
    (fun expression -> ignore (Transform.Convertlist.exp_lst expression))
    [ Dot (xs, segment "field")
    ; BinaryExp (xs, Plus def_seg, Literal (IntLit "1"))
    ; UnaryExp (Not def_seg, xs)
    ; Call (xs, [ list ])
    ; Tuple [ xs ]
    ; Old (def_seg, xs)
    ; Fresh (def_seg, xs)
    ; Forall ([ segment "k" ], xs)
    ; Exists ([ segment "k" ], xs)
    ; Index xs
    ; Slice (Some xs, Some (Literal (IntLit "2")))
    ; Slice (Some xs, None)
    ; Slice (None, Some xs)
    ; Slice (None, None)
    ; IfElseExp (xs, Literal TrueLit, list)
    ];
  let nested_list = Lst [ Literal (IntLit "4") ] in
  let expect_list_assignment name expression =
    let assignments, _ = Transform.Convertlist.exp_lst expression in
    check int name 1 (List.length assignments)
  in
  expect_list_assignment "dot rewrites nested lists"
    (Dot (nested_list, segment "field"));
  expect_list_assignment "binary rewrites nested lists"
    (BinaryExp (nested_list, Plus def_seg, xs));
  expect_list_assignment "unary rewrites nested lists"
    (UnaryExp (Not def_seg, nested_list));
  expect_list_assignment "call rewrites nested list arguments"
    (Call (xs, [ nested_list ]));
  expect_list_assignment "tuple rewrites nested lists"
    (Tuple [ nested_list ]);
  expect_list_assignment "old rewrites nested lists"
    (Old (def_seg, nested_list));
  expect_list_assignment "forall rewrites nested lists"
    (Forall ([ segment "k" ], nested_list));
  expect_list_assignment "index rewrites nested lists"
    (Index nested_list);
  expect_list_assignment "slice rewrites nested lists"
    (Slice (Some nested_list, None));
  expect_list_assignment "conditional rewrites nested lists"
    (IfElseExp (nested_list, xs, xs));
  let reset_input = Program [ Assign (None, [ identifier "reset" ], [ nested_list ]) ] in
  let converted_once = Transform.Convertlist.prog reset_input in
  let converted_twice = Transform.Convertlist.prog reset_input in
  let has_first_temporary = function
    | Program [ Assign (_, [ Identifier (_, Some "templist_1") ], _); Assign _ ] -> true
    | _ -> false
  in
  check bool "list temporary state resets" true (has_first_temporary converted_once);
  check bool "list temporary state resets repeatedly" true (has_first_temporary converted_twice);
  expect_exception "invalid subscript" (function Ast.PyAstError _ -> true | _ -> false)
    (fun () -> Transform.Convertlist.exp_lst (Subscript (xs, Literal (IntLit "1"))))

let test_convertlist_statement_paths () =
  let open Ast in
  let x = identifier "x" in
  Transform.Convertlist.reset ();
  (match Transform.Convertlist.stmt_lst (While ([ Invariant (Lst [ x ]) ], x, [ Pass ])) with
   | [ Assign _; While (_, _, [ Pass; Assign _ ]) ] -> ()
   | _ -> fail "list invariant helper should be refreshed after the body");
  List.iter
    (fun spec -> ignore (Transform.Convertlist.spec_lst spec))
    [ Pre x; Post x; Invariant x; Decreases x; Reads x; Modifies x ];
  List.iter
    (fun statement -> ignore (Transform.Convertlist.stmt_lst statement))
    [ Pass; Break; Continue; Exp x; Assert x
    ; Assign (None, [ x ], [ Lst [ x ] ])
    ; IfElse (x, [ Pass ], [ (x, [ Break ]) ], [ Assert x ])
    ; Return x
    ; While ([ Invariant x ], x, [ Pass ])
    ; For ([ Post x ], [ segment "i" ], x, [ Pass ])
    ; Function ([ Reads x ], segment "f", [], Typ (TInt def_seg), [ Pass ])
    ]

let test_convertcall_and_convertfor_paths () =
  let open Ast in
  let f = identifier "f" in
  let g = identifier "g" in
  let nested = Call (f, [ Call (g, [ Literal (IntLit "1") ]) ]) in
  let assignments, rewritten = Transform.Convertcall.exp_calls nested in
  check int "nested calls become temporaries" 2 (List.length assignments);
  (match rewritten with
   | Identifier (_, Some "tempcall_2") -> ()
   | _ -> fail "outer call should use the second temporary");
  Transform.Convertcall.reset ();
  let quantifier = Forall ([ segment "k" ], Call (identifier "h", [])) in
  let quantifier_assignments, rewritten_quantifier = Transform.Convertcall.exp_calls quantifier in
  check int "quantifier calls stay scoped" 0 (List.length quantifier_assignments);
  (match rewritten_quantifier with
   | Forall (_, Call _) -> ()
   | _ -> fail "calls in quantifiers should stay scoped");
  let lambda = Lambda ([ segment "k" ], Call (identifier "h", [])) in
  let lambda_assignments, rewritten_lambda = Transform.Convertcall.exp_calls lambda in
  check int "lambda calls stay scoped" 0 (List.length lambda_assignments);
  (match rewritten_lambda with
   | Lambda (_, Call _) -> ()
   | _ -> fail "calls in lambdas should stay scoped");
  Transform.Convertcall.reset ();
  let fresh = Fresh (def_seg, Call (identifier "fresh_value", [])) in
  let _, rewritten_fresh = Transform.Convertcall.exp_calls fresh in
  (match rewritten_fresh with
   | Fresh (_, Identifier (_, Some "tempcall_1")) -> ()
   | _ -> fail "Fresh should remain Fresh after call conversion");
  expect_exception "unequal invariant assignment" (function Ast.PyAstError _ -> true | _ -> false)
    (fun () ->
       Transform.Convertcall.assign_to_inv
         (Assign (None, [ identifier "x"; identifier "y" ], [ Literal (IntLit "1") ])));
  let loop =
    For ([ Invariant (Call (identifier "bound", [])) ], [ segment "x" ], identifier "xs",
         [ For ([], [ segment "y" ], identifier "ys", [ Pass ]) ])
  in
  let converted_loop = Transform.Convertfor.prog (Program [ loop ]) in
  (match converted_loop with
   | Program
       [ Assign (_, [ Identifier ((counter_pos, Some "tempfor_1")) ], _)
       ; Assign (_, [ Identifier ((limit_pos, Some "tempfor_2")) ], _)
       ; Assign _
       ; While (specs, _, body) ] ->
     check int "counter source line" 0 counter_pos.pos_lnum;
     check int "counter source column" 0 counter_pos.pos_cnum;
     check int "limit source line" 0 limit_pos.pos_lnum;
     check int "limit source column" 0 limit_pos.pos_cnum;
     check bool "loop invariant retained" true (List.length specs >= 1);
     check bool "nested loop converted" true
       (List.exists (function While _ -> true | _ -> false) body)
   | _ -> fail "for loop should lower to counter state");
  let function_body =
    Function ([], segment "f", [], Typ (TInt def_seg), [ IfElse (Literal TrueLit, [ Pass ], [], [ Break ]); While ([], Literal FalseLit, [ Continue ]) ])
  in
  ignore (Transform.Convertfor.prog (Program [ function_body ]));
  let function_with_spec =
    Function ([ Pre (Call (identifier "guard", [])) ], segment "f", [], Typ (TInt def_seg), [ Exp nested ])
  in
  (match Transform.Convertcall.prog (Program [ function_with_spec ]) with
   | Program [ Function ([ Pre (Call _) ], _, _, _, body) ] ->
     check bool "function body remains transformable" true
       (List.exists (function Assign _ -> true | _ -> false) body)
   | _ -> fail "function call conversion should preserve function");
  ignore (Transform.Convertcall.prog (Program [ IfElse (nested, [ Exp nested ], [ (nested, [ Pass ]) ], [ Return nested ]) ]))

let test_convertcall_expression_paths () =
  let open Ast in
  let x = identifier "x" in
  let call name = Call (identifier name, []) in
  let expressions =
    [ Dot (x, segment "field")
    ; BinaryExp (x, Plus def_seg, x)
    ; UnaryExp (Not def_seg, x)
    ; Lst [ x ]
    ; Tuple [ x ]
    ; Subscript (x, Index (Literal (IntLit "0")))
    ; Index x
    ; Slice (Some x, Some x)
    ; Slice (Some x, None)
    ; Slice (None, Some x)
    ; Slice (None, None)
    ; Len (def_seg, x)
    ; Old (def_seg, x)
    ; Fresh (def_seg, x)
    ; Exists ([ segment "k" ], x)
    ; IfElseExp (x, Literal TrueLit, x)
    ; Lambda ([ segment "k" ], x)
    ; IfElseExp (call "if_true", call "condition", call "if_false")
    ; Index (call "indexed")
    ; Subscript (call "value", call "subscript")
    ; Lst [ call "listed" ]
    ; UnaryExp (Not def_seg, call "negated")
    ]
  in
  List.iter (fun expression -> ignore (Transform.Convertcall.exp_calls expression)) expressions;
  let assignments, rewritten = Transform.Convertcall.exp_calls (IfElseExp (call "if_true", call "condition", call "if_false")) in
  check int "conditional calls are rewritten" 3 (List.length assignments);
  (match rewritten with
   | IfElseExp (Identifier _, Identifier _, Identifier _) -> ()
   | _ -> fail "conditional call expressions should use temporaries");
  let assignments, rewritten = Transform.Convertcall.exp_calls (Index (call "indexed")) in
  check int "index calls are rewritten" 1 (List.length assignments);
  (match rewritten with
   | Index (Identifier _) -> ()
   | _ -> fail "index expressions should use temporaries");
  let assignments, rewritten = Transform.Convertcall.exp_calls (Subscript (call "value", call "subscript")) in
  check int "subscript calls are rewritten" 2 (List.length assignments);
  (match rewritten with
   | Subscript (Identifier _, Identifier _) -> ()
   | _ -> fail "subscript expressions should use temporaries");
  let assignments, rewritten = Transform.Convertcall.exp_calls (Lst [ call "listed" ]) in
  check int "list calls are rewritten" 1 (List.length assignments);
  (match rewritten with
   | Lst [ Identifier _ ] -> ()
   | _ -> fail "list expressions should use temporaries");
  let assignments, rewritten = Transform.Convertcall.exp_calls (UnaryExp (Not def_seg, call "negated")) in
  check int "unary calls are rewritten" 1 (List.length assignments);
  (match rewritten with
   | UnaryExp (_, Identifier _) -> ()
   | _ -> fail "unary expressions should use temporaries");
  let assignments, rewritten =
    Transform.Convertcall.exp_calls
      (BinaryExp (call "left", Plus def_seg, call "right"))
  in
  check int "binary calls are rewritten" 2 (List.length assignments);
  (match rewritten with
   | BinaryExp (Identifier _, _, Identifier _) -> ()
   | _ -> fail "binary expressions should use temporaries");
  let assignments, rewritten =
    Transform.Convertcall.exp_calls (Tuple [ call "first"; call "second" ])
  in
  check int "tuple calls are rewritten" 2 (List.length assignments);
  (match rewritten with
   | Tuple [ Identifier _; Identifier _ ] -> ()
   | _ -> fail "tuple expressions should use temporaries");
  List.iter
    (fun primary ->
       Transform.Convertcall.reset ();
       ignore (Transform.Convertcall.exp_calls (Call (primary, []))))
    [ Dot (x, segment "field")
    ; Call (x, [])
    ; Subscript (x, Index (Literal (IntLit "0")))
    ; IfElseExp (x, Literal TrueLit, x)
    ];
  Transform.Convertcall.reset ();
  ignore (Transform.Convertcall.exp_calls (Call (Identifier def_seg, [])));
  expect_exception "invalid call primary" (function Ast.PyAstError _ -> true | _ -> false)
    (fun () -> Transform.Convertcall.exp_calls (Call (Literal TrueLit, [])));
  ignore (Transform.Convertcall.assign_to_inv (Assign (None, [ x ], [ x ])));
  expect_exception "non-assignment invariant" (function Ast.PyAstError _ -> true | _ -> false)
    (fun () -> Transform.Convertcall.assign_to_inv Pass);
  List.iter
    (fun spec -> ignore (Transform.Convertcall.spec_calls spec))
    [ Pre x; Post x; Invariant x; Decreases x; Reads x; Modifies x ];
  let while_with_call_invariant =
    While ([ Invariant (Call (identifier "bound", [])) ], x, [ Pass ])
  in
  (match Transform.Convertcall.stmt_calls while_with_call_invariant with
   | [ Assign _; While (_, _, [ Pass; Assign _ ]) ] -> ()
   | _ -> fail "call invariant helper should be refreshed after the body");
  let statements =
    [ Pass; Break; Continue; Exp x; Assign (None, [ x ], [ x ])
    ; IfElse (x, [ Pass ], [ (x, [ Break ]) ], [ Continue ])
    ; Return x; Assert x; While ([ Pre x ], x, [ Pass ])
    ; For ([ Post x ], [ segment "i" ], x, [ Pass ])
    ; Function ([ Reads x ], segment "f", [], Typ (TInt def_seg), [ Pass ])
    ]
  in
  List.iter (fun statement -> ignore (Transform.Convertcall.stmt_calls statement)) statements

let test_convertfor_statement_paths () =
  let open Ast in
  let x = identifier "x" in
  List.iter
    (fun statement -> ignore (Transform.Convertfor.stmt_for statement))
    [ Pass; Exp x; Break; Continue; Assign (None, [ x ], [ x ]); Return x; Assert x
    ; IfElse (x, [ Pass ], [ (x, [ Assert x ]) ], [ Break ])
    ; While ([], x, [ Pass ])
    ; Function ([], segment "f", [], Typ (TInt def_seg), [ Pass ])
    ]

let test_generics_paths () =
  let open Ast in
  let type_var name = Call (identifier "TypeVar", [ Literal (StringLit name) ]) in
  let program =
    Program
      [ Assign (None, [ identifier "T" ], [ type_var "T" ])
      ; Assign (None, [ identifier "S" ], [ identifier "T" ])
      ; Assign (None, [ identifier "U" ], [ identifier "S" ])
      ; Assign (None, [ identifier "value" ], [ Literal (IntLit "1") ])
      ]
  in
  (match Transform.Generics.prog program with
   | Program [ Assign (_, [ Identifier (_, Some "value") ], _) ], [ "T"; "S"; "U" ] -> ()
   | _ -> fail "TypeVar declarations should become generic parameters");
  ignore
    (Transform.Generics.prog
       (Program [ Assign (None, [ identifier "T" ], [ type_var "T" ]) ]));
  (match Transform.Generics.prog (Program [ Assign (None, [ identifier "S" ], [ identifier "T" ]) ]) with
   | Program [ Assign _ ], [] -> ()
   | _ -> fail "generic state should reset between programs");
  expect_exception "constrained TypeVar" (function Ast.PyAstError _ -> true | _ -> false)
    (fun () -> Transform.Generics.prog (Program [ Assign (None, [ identifier "T" ], [ Call (identifier "TypeVar", [ Literal (StringLit "T"); Literal (IntLit "1") ]) ]) ]));
  expect_exception "unequal generic assignment" (function Ast.PyAstError _ -> true | _ -> false)
    (fun () -> Transform.Generics.generics (Assign (None, [ identifier "x" ], [])));
  check bool "non-TypeVar call is ignored" true
    (Option.is_none (Transform.Generics.convert_typvar (identifier "T") (Call (identifier "Other", []))));
  check bool "unknown generic identifier is ignored" true
    (Option.is_none (Transform.Generics.convert_typvar (identifier "U") (identifier "Unknown")));
  check bool "non-assignment is preserved" true
    (Option.is_some (fst (Transform.Generics.generics Pass)));
  check bool "non-identifier lhs is ignored" true
    (Option.is_none (Transform.Generics.convert_typvar (Literal TrueLit) (identifier "T")));
  expect_exception "mismatched TypeVar name" (function Ast.PyAstError _ -> true | _ -> false)
    (fun () -> Transform.Generics.convert_typvar (identifier "U") (type_var "T"))

let test_todafnyast_paths () =
  let open Ast in
  let int_typ = TInt def_seg in
  let id_typ = TIdent (segment "Alias") in
  let all_types =
    [ id_typ
    ; int_typ
    ; TFloat def_seg
    ; TBool def_seg
    ; TStr def_seg
    ; TNone def_seg
    ; TObj def_seg
    ; TLst (def_seg, Some int_typ)
    ; TSet (def_seg, Some int_typ)
    ; TDict (def_seg, Some int_typ, Some (TStr def_seg))
    ; TTuple (def_seg, Some [ int_typ; TStr def_seg ])
    ; TTuple (def_seg, None)
    ; TCallable (def_seg, [ int_typ ], TStr def_seg)
    ; TType (def_seg, Some int_typ)
    ]
  in
  List.iter (fun typ -> ignore (Transform.Todafnyast.typ_dfy typ)) all_types;
  ignore (Transform.Todafnyast.check_exp_typ (Typ int_typ));
  ignore (Transform.Todafnyast.check_exp_typ (Identifier (segment "Alias")));
  expect_exception "invalid expression type" (function Transform.Todafnyast.ToDfyError _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.check_exp_typ (Literal TrueLit));
  expect_exception "untyped list" (function Transform.Todafnyast.ToDfyError _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.typ_dfy (TLst (def_seg, None)));
  expect_exception "untyped set" (function Transform.Todafnyast.ToDfyError _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.typ_dfy (TSet (def_seg, None)));
  expect_exception "untyped dict" (function Transform.Todafnyast.ToDfyError _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.typ_dfy (TDict (def_seg, None, Some int_typ)));
  expect_exception "untyped type" (function Transform.Todafnyast.ToDfyError _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.typ_dfy (TType (def_seg, None)));
  let x = identifier "x" in
  let y = identifier "y" in
  let expressions =
    [ x
    ; Dot (x, segment "field")
    ; BinaryExp (x, Plus def_seg, Literal (IntLit "1"))
    ; UnaryExp (Not def_seg, Literal FalseLit)
    ; Literal TrueLit
    ; Literal (FloatLit "1.5")
    ; Literal (StringLit "text")
    ; Literal NoneLit
    ; Call (x, [ y ])
    ; Lst [ x ]
    ; Array [ x ]
    ; Set [ x ]
    ; Dict [ (x, y) ]
    ; Tuple []
    ; Tuple [ x ]
    ; Tuple [ x; y ]
    ; Subscript (x, Index (Literal (IntLit "0")))
    ; Index x
    ; Slice (Some x, Some y)
    ; Slice (Some x, None)
    ; Slice (None, Some y)
    ; Slice (None, None)
    ; Forall ([ segment "k" ], BinaryExp (x, EqEq def_seg, y))
    ; Exists ([ segment "k" ], BinaryExp (x, EqEq def_seg, y))
    ; Len (def_seg, x)
    ; Max (def_seg, x)
    ; Old (def_seg, x)
    ; Fresh (def_seg, x)
    ; Lambda ([ segment "k" ], x)
    ; IfElseExp (x, Literal TrueLit, y)
    ; Typ (TNone def_seg)
    ]
  in
  List.iter (fun expression -> ignore (Transform.Todafnyast.exp_dfy expression)) expressions;
  let all_operators =
    [ NotIn def_seg; In def_seg; Plus def_seg; Minus def_seg; Times def_seg
    ; Divide def_seg; Mod def_seg; NEq def_seg; EqEq def_seg; Lt def_seg
    ; LEq def_seg; Gt def_seg; GEq def_seg; And def_seg; Or def_seg
    ; BiImpl def_seg; Implies def_seg; Explies def_seg ]
  in
  List.iter
    (fun operator -> ignore (Transform.Todafnyast.exp_dfy (BinaryExp (x, operator, y))))
    all_operators;
  ignore (Transform.Todafnyast.exp_dfy (UnaryExp (UMinus def_seg, x)));
  expect_exception "non-None type expression" (function Transform.Todafnyast.ToDfyError _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.exp_dfy (Typ int_typ));
  List.iter
    (fun spec -> ignore (Transform.Todafnyast.spec_dfy spec))
    [ Pre x; Post x; Invariant x; Decreases x; Reads x; Modifies x ];
  let param = (segment "arg", Typ int_typ) in
  ignore (Transform.Todafnyast.param_dfy param);
  let statements =
    [ Exp (Call (x, [ y ]))
    ; Exp (Dot (x, segment "run"))
    ; Assign (Some (Typ int_typ), [ x ], [ Literal (IntLit "1") ])
    ; Assign (Some (Identifier (segment "Alias")), [ x ], [ Literal (IntLit "1") ])
    ; Assign (None, [ x ], [ Literal (IntLit "1") ])
    ; IfElse (Literal TrueLit, [ Pass ], [ (Literal FalseLit, [ Break ]) ], [ Assert x ])
    ; Return x
    ; Assert x
    ; Break
    ; Pass
    ; While ([ Invariant x ], x, [ Pass ])
    ]
  in
  List.iter (fun statement -> ignore (Transform.Todafnyast.stmt_dfy statement)) statements;
  expect_exception "continue statement" (function Transform.Todafnyast.ToDfyError _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.stmt_dfy Continue);
  expect_exception "for statement" (function Transform.Todafnyast.ToDfyError _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.stmt_dfy (For ([], [], x, [])));
  expect_exception "non-call expression statement" (function Transform.Todafnyast.ToDfyError _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.stmt_dfy (Exp x));
  expect_exception "invalid assignment type" (function Transform.Todafnyast.ToDfyError _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.stmt_dfy (Assign (Some (Literal TrueLit), [ x ], [ x ])));
  expect_exception "function statement" (function Assert_failure _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.stmt_dfy (Function ([], segment "f", [], Typ int_typ, [])));
  Transform.Todafnyast.reset ();
  (match Transform.Todafnyast.convert_typsyn (Identifier (segment "Alias")) (Typ int_typ) with
   | Some (D.DTypSynonym _) -> ()
   | _ -> fail "a type assignment should become a Dafny type synonym");
  (match Transform.Todafnyast.convert_typsyn (Identifier (segment "Alias2")) (Identifier (segment "Alias")) with
   | Some (D.DTypSynonym _) -> ()
   | _ -> fail "a type alias should resolve to a known synonym");
  check bool "unknown type alias is ignored" true
    (Option.is_none (Transform.Todafnyast.convert_typsyn (Identifier (segment "Unknown2")) (Identifier (segment "Unknown"))));
  check bool "None type alias is ignored" true
    (Option.is_none (Transform.Todafnyast.convert_typsyn (Identifier (segment "Nothing")) (Typ (TNone def_seg))));
  check bool "non-identifier type alias is ignored" true
    (Option.is_none (Transform.Todafnyast.convert_typsyn (Literal TrueLit) (Typ int_typ)));
  check bool "None is not a top-level declaration" false
    (Transform.Todafnyast.is_toplevel (Assign (None, [ x ], [ Typ (TNone def_seg) ])));
  check bool "ordinary statement is not top-level" false
    (Transform.Todafnyast.is_toplevel Pass);
  check bool "typed assignment is a top-level declaration" true
    (Transform.Todafnyast.is_toplevel (Assign (None, [ x ], [ Typ int_typ ])));
  check bool "function is top-level" true
    (Transform.Todafnyast.is_toplevel (Function ([], segment "f", [], Typ int_typ, [])));
  let function_return = Function ([], segment "f", [ param ], Typ int_typ, [ Return x ]) in
  let function_exp = Function ([], segment "g", [], Typ int_typ, [ Exp x ]) in
  let function_pass = Function ([], segment "h", [], Typ int_typ, [ Pass ]) in
  (match Transform.Todafnyast.func_dfy [] function_return with
   | [ D.DFuncMeth (_, _, _, _, _, Some _) ] -> ()
   | _ -> fail "return function should become a Dafny function method");
  (match Transform.Todafnyast.func_dfy [] function_exp with
   | [ D.DFuncMeth (_, _, _, _, _, Some _) ] -> ()
   | _ -> fail "expression function should become a Dafny function method");
  (match Transform.Todafnyast.func_dfy [] function_pass with
   | [ D.DFuncMeth (_, _, _, _, _, None) ] -> ()
   | _ -> fail "pass function should become a void Dafny function method");
  check bool "return function is recognized" true (Transform.Todafnyast.is_func function_return);
  check bool "expression function is recognized" true (Transform.Todafnyast.is_func function_exp);
  check bool "pass function is recognized" true (Transform.Todafnyast.is_func function_pass);
  check bool "ordinary statement is not a function" false (Transform.Todafnyast.is_func Pass);
  ignore (Transform.Todafnyast.toplevel_dfy [] function_return);
  ignore (Transform.Todafnyast.toplevel_dfy [] (Assign (None, [ x ], [ Typ int_typ ])));
  ignore (Transform.Todafnyast.toplevel_dfy [] Pass);
  expect_exception "unequal top-level declaration" (function Transform.Todafnyast.ToDfyError _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.toplevel_dfy [] (Assign (None, [ x; y ], [ Typ int_typ ])));
  ignore (Transform.Todafnyast.prog_dfy (Program [ function_return; Assign (None, [ x ], [ Literal (IntLit "1") ]) ]))

let test_emitter_paths_and_sourcemaps () =
  let ds name = segment name in
  let id name = D.DIdentifier (ds name) in
  let operators =
    [ D.DNotIn def_seg; D.DIn def_seg; D.DEq def_seg; D.DNEq def_seg
    ; D.DPlus def_seg; D.DMinus def_seg; D.DTimes def_seg; D.DDivide def_seg
    ; D.DMod def_seg; D.DLt def_seg; D.DLEq def_seg; D.DGt def_seg
    ; D.DGEq def_seg; D.DAnd def_seg; D.DOr def_seg; D.DNot def_seg
    ; D.DBiImpl def_seg; D.DImplies def_seg; D.DExplies def_seg
    ]
  in
  List.iter (fun operator -> ignore (Transform.Emitdfy.print_op 0 operator)) operators;
  let types =
    [ D.DVoid; D.DIdentTyp (ds "T", []); D.DIdentTyp (ds "Box", [ D.DInt def_seg ])
    ; D.DInt def_seg; D.DReal def_seg; D.DBool def_seg; D.DString def_seg
    ; D.DChar def_seg; D.DObj def_seg; D.DSeq (def_seg, D.DInt def_seg)
    ; D.DSet (def_seg, D.DInt def_seg); D.DMap (def_seg, D.DInt def_seg, D.DString def_seg)
    ; D.DArray (def_seg, D.DInt def_seg); D.DTuple (def_seg, [ D.DInt def_seg ])
    ; D.DFunTyp (def_seg, [ D.DInt def_seg ], D.DBool def_seg)
    ]
  in
  List.iter (fun typ -> ignore (Transform.Emitdfy.print_type 0 typ)) types;
  let render_type typ =
    Transform.Emitdfy.reset ();
    Transform.Emitdfy.print_type 0 typ
  in
  check string "identifier type rendering" "T" (render_type (D.DIdentTyp (ds "T", [])));
  check string "generic type rendering" "Box<int>"
    (render_type (D.DIdentTyp (ds "Box", [ D.DInt def_seg ])));
  check string "integer type rendering" "int" (render_type (D.DInt def_seg));
  check string "real type rendering" "real" (render_type (D.DReal def_seg));
  check string "boolean type rendering" "bool" (render_type (D.DBool def_seg));
  check string "string type rendering" "string" (render_type (D.DString def_seg));
  check string "character type rendering" "char" (render_type (D.DChar def_seg));
  check string "object type rendering" "object" (render_type (D.DObj def_seg));
  check string "sequence type rendering" "seq<int>"
    (render_type (D.DSeq (def_seg, D.DInt def_seg)));
  check string "set type rendering" "set<int>"
    (render_type (D.DSet (def_seg, D.DInt def_seg)));
  check string "map type rendering" "map<int, string>"
    (render_type (D.DMap (def_seg, D.DInt def_seg, D.DString def_seg)));
  check string "tuple type rendering" "(int)"
    (render_type (D.DTuple (def_seg, [ D.DInt def_seg ])));
  check string "function type rendering" "(int) -> bool"
    (render_type (D.DFunTyp (def_seg, [ D.DInt def_seg ], D.DBool def_seg)));
  let check_type_source name typ value =
    Transform.Emitdfy.reset ();
    ignore (Transform.Emitdfy.print_type 0 typ);
    check bool name true
      (has_substring (Transform.Emitdfy.print_sourcemap !Transform.Emitdfy.sm) value)
  in
  check_type_source "identifier type source map" (D.DIdentTyp (segment "T-source", [])) "T-source";
  check_type_source "integer type source map" (D.DInt (segment "int-source")) "int-source";
  check_type_source "real type source map" (D.DReal (segment "real-source")) "real-source";
  check_type_source "boolean type source map" (D.DBool (segment "bool-source")) "bool-source";
  check_type_source "string type source map" (D.DString (segment "string-source")) "string-source";
  check_type_source "character type source map" (D.DChar (segment "char-source")) "char-source";
  check_type_source "object type source map" (D.DObj (segment "object-source")) "object-source";
  check_type_source "sequence type source map" (D.DSeq (segment "seq-source", D.DInt def_seg)) "seq-source";
  check_type_source "set type source map" (D.DSet (segment "set-source", D.DInt def_seg)) "set-source";
  check_type_source "map type source map"
    (D.DMap (segment "map-source", D.DInt def_seg, D.DString def_seg)) "map-source";
  check_type_source "tuple type source map" (D.DTuple (segment "tuple-source", [ D.DInt def_seg ])) "tuple-source";
  check_type_source "function type source map"
    (D.DFunTyp (segment "function-source", [ D.DInt def_seg ], D.DBool def_seg)) "function-source";
  let expressions =
    [ id "x"; D.DDot (id "x", ds "field")
    ; D.DBinary (id "x", D.DPlus def_seg, D.DIntLit "1")
    ; D.DUnary (D.DNot def_seg, D.DFalse)
    ; D.DIntLit "1"; D.DRealLit "1.5"; D.DTrue; D.DFalse
    ; D.DStringLit "text"; D.DNull; D.DThis; D.DEmptyExpr
    ; D.DCallExpr (id "f", [ id "x" ]); D.DSeqExpr [ id "x" ]
    ; D.DArrayExpr [ id "x" ]; D.DSetExpr [ id "x" ]
    ; D.DMapExpr [ (id "x", D.DIntLit "1") ]; D.DSubscript (id "x", D.DIndex (D.DIntLit "0"))
    ; D.DIndex (id "x"); D.DSlice (Some (D.DIntLit "1"), Some (D.DIntLit "2"))
    ; D.DSlice (Some (D.DIntLit "1"), None); D.DSlice (None, Some (D.DIntLit "2"))
    ; D.DSlice (None, None); D.DForall ([ ds "k" ], D.DTrue)
    ; D.DExists ([ ds "k" ], D.DFalse); D.DLen (def_seg, id "x")
    ; D.DOld (def_seg, id "x"); D.DFresh (def_seg, id "x")
    ; D.DLambda ([ (ds "x", D.DVoid) ], [], id "x")
    ; D.DIfElseExpr (D.DTrue, D.DIntLit "1", D.DIntLit "2")
    ; D.DTupleExpr [ id "x"; id "y" ]
    ]
  in
  Transform.Emitdfy.reset ();
  List.iter (fun expression -> ignore (Transform.Emitdfy.print_exp 0 expression)) expressions;
  let render_exp expression =
    Transform.Emitdfy.reset ();
    Transform.Emitdfy.print_exp 0 expression
  in
  check string "identifier rendering" "x" (render_exp (id "x"));
  check string "dot rendering" "x.field" (render_exp (D.DDot (id "x", ds "field")));
  check string "binary rendering" "(x + 1)"
    (render_exp (D.DBinary (id "x", D.DPlus def_seg, D.DIntLit "1")));
  check string "unary rendering" "(!false)"
    (render_exp (D.DUnary (D.DNot def_seg, D.DFalse)));
  check string "integer literal rendering" "1" (render_exp (D.DIntLit "1"));
  check string "real literal rendering" "1.5" (render_exp (D.DRealLit "1.5"));
  check string "true rendering" "true" (render_exp D.DTrue);
  check string "false rendering" "false" (render_exp D.DFalse);
  check string "string literal rendering" "\"text\"" (render_exp (D.DStringLit "text"));
  check string "null rendering" "null" (render_exp D.DNull);
  check string "this rendering" "this" (render_exp D.DThis);
  check string "empty expression rendering" "" (render_exp D.DEmptyExpr);
  check string "call rendering" "f(x)" (render_exp (D.DCallExpr (id "f", [ id "x" ])));
  check string "sequence rendering" "[x, y]"
    (render_exp (D.DSeqExpr [ id "x"; id "y" ]));
  check string "array rendering" "[x, y]"
    (render_exp (D.DArrayExpr [ id "x"; id "y" ]));
  check string "set rendering" "{x, y}"
    (render_exp (D.DSetExpr [ id "x"; id "y" ]));
  check string "map rendering" "map[x := 1, y := 2]"
    (render_exp (D.DMapExpr [ (id "x", D.DIntLit "1"); (id "y", D.DIntLit "2") ]));
  check string "subscript rendering" "x0"
    (render_exp (D.DSubscript (id "x", D.DIndex (D.DIntLit "0"))));
  check string "index rendering" "x" (render_exp (D.DIndex (id "x")));
  check string "range slice rendering" "[1..2]"
    (render_exp (D.DSlice (Some (D.DIntLit "1"), Some (D.DIntLit "2"))));
  check string "lower slice rendering" "[1]"
    (render_exp (D.DSlice (Some (D.DIntLit "1"), None)));
  check string "upper slice rendering" "[2]"
    (render_exp (D.DSlice (None, Some (D.DIntLit "2"))));
  check string "empty slice rendering" "[]" (render_exp (D.DSlice (None, None)));
  check string "forall rendering" "forall k :: true"
    (render_exp (D.DForall ([ ds "k" ], D.DTrue)));
  check string "exists rendering" "existsk :: false"
    (render_exp (D.DExists ([ ds "k" ], D.DFalse)));
  check string "length rendering" "|x|" (render_exp (D.DLen (def_seg, id "x")));
  check string "old rendering" "old(x)" (render_exp (D.DOld (def_seg, id "x")));
  check string "fresh rendering" "fresh(x)" (render_exp (D.DFresh (def_seg, id "x")));
  check string "lambda rendering" "(x) => x"
    (render_exp (D.DLambda ([ (ds "x", D.DVoid) ], [], id "x")));
  check string "lambda specification rendering" "(x)requires true => x"
    (render_exp
       (D.DLambda ([ (ds "x", D.DVoid) ], [ D.DRequires D.DTrue ], id "x")));
  check string "conditional rendering" "if true then 1 else 2"
    (render_exp (D.DIfElseExpr (D.DTrue, D.DIntLit "1", D.DIntLit "2")));
  check string "tuple rendering" "(x, y)"
    (render_exp (D.DTupleExpr [ id "x"; id "y" ]));
  Transform.Emitdfy.reset ();
  Transform.Emitdfy.curr_func := "stale";
  Transform.Emitdfy.reset ();
  check string "emitter resets current function" "" !Transform.Emitdfy.curr_func;
  ignore (Transform.Emitdfy.print_ident 0 (ds "x"));
  ignore (Transform.Emitdfy.print_ident 0 (ds "y"));
  check bool "source map tracks column changes" true
    (has_substring (Transform.Emitdfy.print_sourcemap !Transform.Emitdfy.sm) "(1, 2)");
  Transform.Emitdfy.reset ();
  ignore (Transform.Emitdfy.print_ident 0 (ds "x"));
  ignore (Transform.Emitdfy.newline ());
  ignore (Transform.Emitdfy.print_ident 0 (ds "y"));
  check bool "source map tracks line changes" true
    (has_substring (Transform.Emitdfy.print_sourcemap !Transform.Emitdfy.sm) "(2, 1)");
  Transform.Emitdfy.reset ();
  check string "unbound assignment declaration" "var x;"
    (Transform.Emitdfy.print_stmt 0 (D.DAssign (None, [ ds "x" ], [])));
  check string "repeated assignment reuses declaration" "x;"
    (Transform.Emitdfy.print_stmt 0 (D.DAssign (None, [ ds "x" ], [])));
  check string "typed assignment rendering" "var y: int := 1;"
    (Transform.Emitdfy.print_stmt 0
       (D.DAssign (Some (D.DInt def_seg), [ ds "y" ], [ D.DIntLit "1" ])));
  check string "typed assignment records declaration" "y;"
    (Transform.Emitdfy.print_stmt 0 (D.DAssign (None, [ ds "y" ], [])));
  check string "parameter rendering" "x: int"
    (Transform.Emitdfy.print_param 0 (ds "x", D.DInt def_seg));
  check string "void return rendering" ""
    (Transform.Emitdfy.print_rets 0 [ D.DVoid ]);
  check string "return rendering" "(res: int)"
    (Transform.Emitdfy.print_rets 0 [ D.DInt def_seg ]);
  check string "assume rendering" "assume true;"
    (Transform.Emitdfy.print_stmt 0 (D.DAssume D.DTrue));
  check string "assert rendering" "assert true;"
    (Transform.Emitdfy.print_stmt 0 (D.DAssert D.DTrue));
  check string "break rendering" "break;"
    (Transform.Emitdfy.print_stmt 0 D.DBreak);
  check string "call statement rendering" "f(1);"
    (Transform.Emitdfy.print_stmt 0 (D.DCallStmt (id "f", [ D.DIntLit "1" ])));
  check string "return statement rendering" "return 1;"
    (Transform.Emitdfy.print_stmt 0 (D.DReturn [ D.DIntLit "1" ]));
  check string "if statement rendering" "if true {\n  break;\n}"
    (Transform.Emitdfy.print_stmt 0 (D.DIf (D.DTrue, [ D.DBreak ], [], [])));
  check string "if else statement rendering"
    "if true {\n  break;\n} else if false {\n  break;\n} else {\n  assert true;\n}"
    (Transform.Emitdfy.print_stmt 0
       (D.DIf (D.DTrue, [ D.DBreak ],
               [ (D.DFalse, [ D.DBreak ]) ], [ D.DAssert D.DTrue ])));
  check string "while statement rendering" "while true\n  invariant true\n{\n  break;\n}"
    (Transform.Emitdfy.print_stmt 0
       (D.DWhile ([ D.DInvariant D.DTrue ], D.DTrue, [ D.DBreak ])));
  let render_spec spec =
    Transform.Emitdfy.reset ();
    Transform.Emitdfy.print_spec 0 spec
  in
  check string "requires rendering" "requires true"
    (render_spec (D.DRequires D.DTrue));
  check string "modifies rendering" "modifies true"
    (render_spec (D.DModifies D.DTrue));
  let render_toplevel declaration =
    Transform.Emitdfy.reset ();
    Transform.Emitdfy.print_toplevel 0 declaration
  in
  check string "type declaration rendering" "type Alias = int"
    (render_toplevel (D.DTypSynonym (ds "Alias", Some (D.DInt def_seg))));
  check string "bare type declaration rendering" "type Alias"
    (render_toplevel (D.DTypSynonym (ds "Alias", None)));
  check string "method declaration rendering" "method m()\n\n"
    (render_toplevel (D.DMeth ([], ds "m", [], [], [], None)));
  check string "function declaration rendering"
    "function f(): (res: int)\n\n{\n  true\n}\n"
    (render_toplevel (D.DFuncMeth ([], ds "f", [], [], D.DInt def_seg, Some D.DTrue)));
  let method_with_spec =
    render_toplevel
      (D.DMeth ([ D.DEnsures D.DTrue ], ds "spec_m", [], [], [], None))
  in
  check bool "method specification indentation" true
    (has_substring method_with_spec "\n  ensures true");
  check bool "method specification has no extra indentation" false
    (has_substring method_with_spec "\n   ensures true");
  let method_with_body =
    render_toplevel
      (D.DMeth ([], ds "body_m", [], [], [], Some [ D.DReturn [ D.DIntLit "1" ] ]))
  in
  check bool "method body indentation" true
    (has_substring method_with_body "\n  return 1;");
  List.iter
    (fun spec -> ignore (Transform.Emitdfy.print_spec 0 spec))
    [ D.DRequires D.DTrue; D.DEnsures D.DTrue; D.DInvariant D.DTrue
    ; D.DDecreases (D.DIntLit "1"); D.DReads D.DThis; D.DModifies D.DThis ];
  let statements =
    [ D.DEmptyStmt; D.DAssume D.DTrue; D.DAssert D.DTrue; D.DBreak
    ; D.DAssign (None, [], []); D.DAssign (None, [ ds "x" ], [])
    ; D.DAssign (Some (D.DInt def_seg), [ ds "y" ], [ D.DIntLit "1" ])
    ; D.DCallStmt (id "f", [ D.DIntLit "1" ])
    ; D.DIf (D.DTrue, [ D.DAssert D.DTrue ], [ (D.DFalse, [ D.DBreak ]) ], [ D.DEmptyStmt ])
    ; D.DWhile ([ D.DInvariant D.DTrue ], D.DTrue, [ D.DBreak ])
    ; D.DReturn [ D.DIntLit "1" ]
    ]
  in
  Transform.Emitdfy.reset ();
  List.iter (fun statement -> ignore (Transform.Emitdfy.print_stmt 0 statement)) statements;
  Transform.Emitdfy.reset ();
  ignore (Transform.Emitdfy.print_stmt 0 (D.DAssign (None, [ ds "x" ], [ D.DIntLit "1" ])));
  ignore (Transform.Emitdfy.print_stmt 0 (D.DAssign (None, [ ds "x" ], [ D.DIntLit "2" ])));
  ignore (Transform.Emitdfy.print_stmt 0 (D.DIf (D.DTrue, [ D.DBreak ], [], [])));
  ignore (Transform.Emitdfy.print_rets 0 []);
  ignore (Transform.Emitdfy.print_rets 0 [ D.DVoid ]);
  ignore (Transform.Emitdfy.print_rets 0 [ D.DInt def_seg ]);
  let top_levels =
    [ D.DTypSynonym (ds "Alias", Some (D.DInt def_seg))
    ; D.DTypSynonym (ds "BareAlias", None)
    ; D.DFuncMeth ([ D.DEnsures D.DTrue ], ds "f", [ "T" ], [], D.DInt def_seg, Some D.DTrue)
    ; D.DFuncMeth ([], ds "void_f", [], [], D.DVoid, None)
    ; D.DMeth ([ D.DRequires D.DTrue ], ds "m", [ "T" ], [ (ds "x", D.DInt def_seg) ], [ D.DInt def_seg ], Some [ D.DReturn [ D.DIntLit "1" ] ])
    ]
  in
  let source = Transform.Emitdfy.print_prog (D.DProg ("", top_levels)) in
  check bool "emitter prints declarations" true (String.length source > 0);
  let source_again = Transform.Emitdfy.print_prog (D.DProg ("", top_levels)) in
  check string "emitter is repeatable" source source_again;
  let mapping = ref [ ((2, 3), segment "nearest"); ((1, 1), segment "other") ] in
  check string "nearest source map entry" "nearest" (seg_val (Transform.Emitdfy.nearest_seg !mapping 2 3));
  check string "empty source map fallback" "Line: 0  Column: 0" (print_seg (Transform.Emitdfy.nearest_seg [] 10 10));
  let ties = [ ((2, 1), segment "first"); ((2, 5), segment "second") ] in
  check string "nearest source map tie by column" "first" (seg_val (Transform.Emitdfy.nearest_seg ties 2 3));
  let closer = [ ((2, 1), segment "first"); ((2, 5), segment "second") ] in
  check string "nearest source map closer column" "second" (seg_val (Transform.Emitdfy.nearest_seg closer 2 6));
  check string "source map rendering"
    "(2, 3):  Line: 1  Column: 1  Value: nearest\n(1, 1):  Line: 1  Column: 1  Value: other"
    (Transform.Emitdfy.print_sourcemap !mapping)

let test_report_paths () =
  let source_map =
    ref
      [ ((1, 2), segment ~line:4 ~column:6 "first")
      ; ((2, 1), segment ~line:8 ~column:3 "second")
      ]
  in
  let output = "program.dfy(1,2): Error, a postcondition might not hold\n" in
  (match Run.Report.verification_errors ~sourcemap:source_map output with
   | Some errors ->
     check string "diagnostic location is replaced in the first field"
       "Line: 4  Column: 6  Value: first,  Error, a postcondition might not hold"
       errors;
     check bool "verification error is mapped" true (has_substring errors "first");
     check bool "original verifier path is replaced" false
       (has_substring errors "program.dfy")
   | None -> fail "verification error should be recognized");
  check bool "non-error output has no locations" true
    (Option.is_none (Run.Report.verification_errors ~sourcemap:source_map "verified\n"));
  let missing_location_map =
    ref
      [ ((0, 100), segment ~line:0 ~column:100 "zero")
      ; ((2, 0), segment ~line:2 ~column:0 "two")
      ]
  in
  check string "missing line defaults to zero" "Line: 0  Column: 100  Value: zero"
    (Run.Report.replace_num ~sourcemap:missing_location_map "no numeric location");
  ignore (Run.Report.replace_num "1,2");
  ignore (Run.Report.verification_errors "verified\n");
  let reported =
    let read_fd, write_fd = Unix.pipe () in
    let saved_stderr = Unix.dup Unix.stderr in
    Unix.dup2 write_fd Unix.stderr;
    Unix.close write_fd;
    (try
       Run.Report.report ~sourcemap:source_map
         (output ^ "verifier finished with 2 verified, 0 errors\n");
       Stdlib.flush Stdlib.stderr
     with exn ->
       Unix.dup2 saved_stderr Unix.stderr;
       Unix.close saved_stderr;
       Unix.close read_fd;
       raise exn);
    Unix.dup2 saved_stderr Unix.stderr;
    Unix.close saved_stderr;
    let buffer = Buffer.create 128 in
    let bytes = Bytes.create 128 in
    let rec read_all () =
      match Unix.read read_fd bytes 0 (Bytes.length bytes) with
      | 0 -> ()
      | count ->
        Buffer.add_subbytes buffer bytes 0 count;
        read_all ()
    in
    read_all ();
    Unix.close read_fd;
    Buffer.contents buffer
  in
  check bool "report prints mapped diagnostics" true (has_substring reported "first");
  Run.Report.verification_summary "verifier finished with 2 verified, 0 errors\n";
  expect_exception "malformed verifier summary" (function Run.Report.ReportError _ -> true | _ -> false)
    (fun () -> Run.Report.verification_summary "no summary\n")

let test_pipeline_failure_and_artifact_paths () =
  let root = Filename.temp_file "dafny-of-python-keep-" ".tmp" in
  Sys.remove root;
  Unix.mkdir root 0o700;
  let runner (command : Run.Pipeline.command) =
    if String.equal command.program "mypy" then
      ({ exit_code = 4; stdout = "mypy stdout"; stderr = "mypy stderr" } : Run.Pipeline.command_result)
    else
      ({ exit_code = 9; stdout = "dafny stdout"; stderr = "dafny stderr" } : Run.Pipeline.command_result)
  in
  let base = Run.Pipeline.default_config ~prelude:"prelude.dfy" ~list_library:"list.dfy" in
  let config = { base with temp_root = Some root; keep_artifacts = true; runner } in
  let result = Run.Pipeline.run ~config "x = 1\n" in
  check int "verification failure is fatal" 1 (Run.Pipeline.exit_code result);
  check int "typecheck status is preserved" 4 result.typecheck.exit_code;
  check int "verification status is preserved" 9 result.verification.exit_code;
  (match result.working_directory with
   | Some directory ->
     check int "temporary directory permissions" 0o700
       (Unix.(stat directory).st_perm);
     check bool "kept Python artifact" true (Sys.file_exists (Filename.concat directory "program.py"));
     check bool "kept Dafny artifact" true (Sys.file_exists (Filename.concat directory "program.dfy"));
     Sys.remove (Filename.concat directory "program.py");
     Sys.remove (Filename.concat directory "program.dfy");
     Unix.rmdir directory
   | None -> fail "keep_artifacts should expose the run directory");
  check bool "temporary root is empty after manual cleanup" true (Array.length (Sys.readdir root) = 0);
  Unix.rmdir root;
  let missing = Run.Pipeline.default_runner { program = "/definitely/missing/dafny-of-python"; args = [] } in
  check int "missing executable status" 127 missing.exit_code;
  let success =
    { result with
      typecheck = { exit_code = 0; stdout = ""; stderr = "" }
    ; verification = { exit_code = 0; stdout = ""; stderr = "" }
    }
  in
  check int "successful pipeline status" 0 (Run.Pipeline.exit_code success);
  let typecheck_only_failure =
    { success with typecheck = { exit_code = 2; stdout = ""; stderr = "" } }
  in
  check int "mypy failure status" 2 (Run.Pipeline.exit_code typecheck_only_failure)

let test_pipeline_system_and_exception_paths () =
  let output = Run.Pipeline.default_runner
      { program = "/bin/sh"; args = [ "-c"; "printf stdout; printf stderr >&2" ] }
  in
  check int "shell command succeeds" 0 output.exit_code;
  check string "stdout is captured" "stdout" output.stdout;
  check string "stderr is captured" "stderr" output.stderr;
  let signalled = Run.Pipeline.default_runner
      { program = "/bin/sh"; args = [ "-c"; "kill -TERM $$" ] }
  in
  check bool "signalled command has non-zero status" true (signalled.exit_code <> 0);
  let read_fd, write_fd = Unix.pipe () in
  Unix.close read_fd;
  Run.Pipeline.close_noerr write_fd;
  Run.Pipeline.close_noerr write_fd;
  check int "signalled status maps to shell code" 130
    (Run.Pipeline.status_code (Unix.WSIGNALED 2));
  check int "stopped status maps to shell code" 130
    (Run.Pipeline.status_code (Unix.WSTOPPED 2));
  Run.Pipeline.remove_file "/definitely/missing/dafny-of-python-file";
  Run.Pipeline.cleanup_directory
    { (Run.Pipeline.default_config ~prelude:"prelude" ~list_library:"list") with keep_artifacts = false }
    "/definitely/missing/dafny-of-python-directory" [];
  let root = Filename.temp_file "dafny-of-python-exception-" ".tmp" in
  Sys.remove root;
  Unix.mkdir root 0o700;
  let base = Run.Pipeline.default_config ~prelude:"prelude.dfy" ~list_library:"list.dfy" in
  let exploding _ = failwith "runner exploded" in
  let config = { base with temp_root = Some root; runner = exploding } in
  expect_exception "runner exceptions are re-raised" (function Failure _ -> true | _ -> false)
    (fun () -> Run.Pipeline.run ~config "x = 1\n");
  check bool "exception cleanup removes temporary files" true (Array.length (Sys.readdir root) = 0);
  Unix.rmdir root

let () =
  run "dafny-of-python"
    [ ("parser", [ test_case "typed assignment" `Quick test_parser_assignment
                  ; test_case "specifications and control flow" `Quick test_parser_specs_and_control_flow
                  ; test_case "fresh expression" `Quick test_parser_fresh
                  ; test_case "entry points and errors" `Quick test_parser_entry_points_and_errors
                  ; test_case "nice parser wrapper" `Quick test_nice_parser_wrapper_paths
                  ; test_case "expression and type forms" `Quick test_parser_expression_and_type_forms
                  ; test_case "AST utilities" `Quick test_ast_utilities
                  ; test_case "AST serializers and subtyping" `Quick test_ast_serializers_and_subtyping ])
    ; ("transforms", [ test_case "call state reset" `Quick test_transform_state_resets
                      ; test_case "emitter state reset" `Quick test_emitter_resets_state
                      ; test_case "Dafny 4 function syntax" `Quick test_dafny4_function_syntax
                      ; test_case "list conversion paths" `Quick test_convertlist_paths
                      ; test_case "list statement paths" `Quick test_convertlist_statement_paths
                      ; test_case "call and for conversion" `Quick test_convertcall_and_convertfor_paths
                      ; test_case "for statement paths" `Quick test_convertfor_statement_paths
                      ; test_case "generic conversion" `Quick test_generics_paths
                      ; test_case "call expression paths" `Quick test_convertcall_expression_paths
                      ; test_case "Dafny AST conversion" `Quick test_todafnyast_paths
                      ; test_case "emitter and source maps" `Quick test_emitter_paths_and_sourcemaps ])
    ; ("report", [ test_case "report parsing" `Quick test_report_paths ])
    ; ("pipeline", [ test_case "injected commands and cleanup" `Quick test_pipeline_injects_commands_and_cleans_files
                    ; test_case "failure and artifact paths" `Quick test_pipeline_failure_and_artifact_paths
                    ; test_case "system and exception paths" `Quick test_pipeline_system_and_exception_paths ])
    ]
