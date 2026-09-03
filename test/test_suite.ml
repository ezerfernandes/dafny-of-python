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
  check bool "legacy function syntax is not emitted" false (has_substring generated "function method");
  let method_program =
    Ast.Program
      (parse_program
         "def method_form(x: int) -> int:\n  y = x + 1\n  return y\n\n# pre len(xs) > 1\ndef tail(xs: list[int]) -> list[int]:\n  return xs[1:]\n\ndef tail_caller(xs: list[int]) -> list[int]:\n  return tail(xs)\n\ndef mutate(xs: list[int]) -> None:\n  xs.append(2)\n\ndef alias_mutate(xs: list[int]) -> None:\n  ys = xs\n  ys.append(2)\n\ndef caller() -> int:\n  return method_form(1)\n")
  in
  let method_ast = Transform.Todafnyast.prog_dfy method_program in
  let method_source, _ = Transform.Emitdfy.print_prog_with_sourcemap method_ast
  in
  check bool "lowered multi-statement functions are methods" true
    (has_substring method_source "method method_form");
  check bool "list-slice functions are methods" true
    (has_substring method_source "method tail");
  check bool "callers of list-slice methods are synchronized" true
    (has_substring method_source "method tail_caller");
  check bool "list slices call the runtime method" true
    (has_substring method_source "rangeLower");
  check bool "methods forwarding list arguments carry a frame" true
    (match method_ast with
     | D.DProg (_, declarations) ->
       List.exists
         (function
          | D.DMeth (specifications, (_, Some "tail_caller"), _, _, _, _) ->
            List.exists
              (function
               | D.DModifies (D.DIdentifier (_, Some "xs")) -> true
               | _ -> false)
              specifications
          | _ -> false)
         declarations);
  check bool "None expression-only functions emit statements" true
    (match method_ast with
     | D.DProg (_, declarations) ->
       List.exists
         (function
          | D.DMeth (_, (_, Some "mutate"), _, _, [ D.DVoid ], Some [ D.DCallStmt _ ]) -> true
          | _ -> false)
         declarations);
  check bool "alias-mutating methods carry a frame" true
    (match method_ast with
     | D.DProg (_, declarations) ->
       List.exists
         (function
          | D.DMeth (specifications, (_, Some "alias_mutate"), _, _, [ D.DVoid ], _) ->
            List.exists
              (function
               | D.DModifies (D.DIdentifier (_, Some "xs")) -> true
               | _ -> false)
              specifications
          | _ -> false)
         declarations);
  check bool "callers use the synchronized method signature" true
    (has_substring method_source "method caller");
  check bool "method calls are hoisted out of caller expressions" true
    (has_substring method_source "return lowered_")

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
  (match Pyparse.Parser.parse_string "while True:\n  continue\n" with
   | Ast.Program [ Ast.While (_, _, [ Ast.Continue ]) ] -> ()
   | _ -> fail "continue should be parsed as a control-flow statement");
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
  expect "empty lexer output" (function Failure _ -> true | _ -> false)
    (fun () -> ignore ((Pyparse.Indenter.flatten (fun _ -> [])) (Lexing.from_string "")));
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

let test_phase2_parser_forms () =
  let open Ast in
  let singleton source =
    match parse_program source with
    | [ Exp (SingletonTuple (comma, Identifier (_, Some "value"))) ] ->
      check string "singleton tuple comma source" "," (seg_val comma)
    | _ -> fail "comma-bearing singleton tuple was not preserved"
  in
  singleton "value,\n";
  singleton "(value,)\n";
  (match parse_program "(value)\n" with
   | [ Exp (Identifier (_, Some "value")) ] -> ()
   | _ -> fail "parenthesized expressions should not become tuples");
  (match parse_program "value = (first, second)\n" with
   | [ Assign (_, _, [ Tuple [ Identifier (_, Some "first"); Identifier (_, Some "second") ] ]) ] -> ()
   | _ -> fail "multi-element tuples should remain tuples");
  (match parse_program "value = first < second > third\n" with
   | [ Assign (_, _, [ CompareChain (_, [ (Lt _, _); (Gt _, _) ]) ]) ] -> ()
   | _ -> fail "comparison chains should use a flat source node");
  (match parse_program "value = first in values != missing\n" with
   | [ Assign (_, _, [ CompareChain (_, [ (In _, _); (NEq _, _) ]) ]) ] -> ()
   | _ -> fail "membership comparison chains should preserve operators");
  (try
     ignore (Pyparse.Parser.parse_string "()\n");
     fail "empty tuple should remain unsupported"
   with
   | Pyparse.Parser.ParseError _ -> ())

let test_phase3_collection_parser_forms () =
  let open Ast in
  (match parse_program "values = {1, 2}\n" with
   | [ Assign (_, _, [ Set [ Literal (IntLit "1"); Literal (IntLit "2") ] ]) ] -> ()
   | _ -> fail "set displays should preserve their element list");
  (match parse_program "mapping = {1: 2, 3: 4}\n" with
   | [ Assign (_, _, [ Dict [ (Literal (IntLit "1"), Literal (IntLit "2")); (Literal (IntLit "3"), Literal (IntLit "4")) ] ]) ] -> ()
   | _ -> fail "dictionary displays should preserve key/value entries");
  let call_name source expected =
    match parse_program source with
    | [ Assign (_, _, [ Call (Identifier (_, Some name), []) ]) ] ->
      check bool (source ^ " constructor") true
        (String.equal (String.lowercase_ascii name) expected
         || String.equal (String.lowercase_ascii name) (expected ^ "f"))
    | _ -> fail (source ^ " should parse as a constructor call")
  in
  call_name "values = set()\n" "set";
  call_name "mapping = dict()\n" "dict";
  (match parse_program "value = left | middle & right\n" with
   | [ Assign (_, _, [ BinaryExp (Identifier (_, Some "left"), BitOr _, BinaryExp (Identifier (_, Some "middle"), BitAnd _, Identifier (_, Some "right"))) ]) ] -> ()
   | _ -> fail "set union and intersection precedence should be preserved");
  (match parse_program "value = key in values | other\n" with
   | [ Assign (_, _, [ CompareChain (_, [ (In _, BinaryExp (_, BitOr _, _)) ]) ]) ] -> ()
   | _ -> fail "membership should accept a set algebra expression")

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
    ; Gt s; GEq s; And s; Or s; NotIn s; In s; BiImpl s; Implies s; Explies s
    ; BitOr s; BitAnd s ]
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
    ; CompareChain (xs, [ Lt def_seg, xs; Gt def_seg, xs ])
    ; UnaryExp (Not def_seg, xs)
    ; Call (xs, [ list ])
    ; Tuple [ xs ]
    ; SingletonTuple (segment ",", xs)
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
  expect_list_assignment "singleton tuple rewrites nested lists"
    (SingletonTuple (segment ",", nested_list));
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
    ; CompareChain (x, [ Lt def_seg, call "middle"; Gt def_seg, call "last" ])
    ; UnaryExp (Not def_seg, x)
    ; Lst [ x ]
    ; Tuple [ x ]
    ; SingletonTuple (segment ",", x)
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
  ignore
    (Transform.Convertcall.exp_calls_scoped
       (CompareChain (x, [ Lt def_seg, SingletonTuple (segment ",", x) ])));
  ignore (Transform.Convertcall.exp_calls_scoped (SingletonTuple (segment ",", x)));
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

let test_semantic_lowering_paths () =
  let open Ast in
  let int_type = TInt def_seg in
  let list_type = TLst (def_seg, Some int_type) in
  let sequence_type = TGeneric (segment "seq", [ int_type ]) in
  let map_type = TDict (def_seg, Some (TStr def_seg), Some int_type) in
  let tuple_type = TTuple (def_seg, Some [ int_type; TStr def_seg ]) in
  let xs = identifier "xs" in
  let sequence = identifier "sequence" in
  let mapping = identifier "mapping" in
  let tuple = identifier "tuple" in
  let environment =
    Transform.Semantic.empty
    |> fun environment -> Transform.Semantic.bind environment "xs" list_type
    |> fun environment -> Transform.Semantic.bind environment "sequence" sequence_type
    |> fun environment -> Transform.Semantic.bind environment "mapping" map_type
    |> fun environment -> Transform.Semantic.bind environment "tuple" tuple_type
  in
  List.iter
    (fun name -> ignore (Transform.Semantic.normalize_type (TIdent (segment name))))
    [ "list"; "seq"; "sequence"; "set"; "dict"; "map"; "tuple"; "array" ];
  ignore (Transform.Semantic.bind { Transform.Semantic.scopes = []; functions = []; classes = []; memberships = []; known_map_keys = []; map_aliases = []; list_aliases = []; iterated_lists = []; iterated_maps = [] } "ignored" int_type);
  ignore (Transform.Semantic.annotation (Typ int_type));
  ignore (Transform.Semantic.annotation (Identifier (segment "Alias")));
  ignore (Transform.Semantic.annotation (Literal TrueLit));
  let lower expression = Transform.Lowering.expression ~environment expression in
  (match Transform.Lowering.type_dfy list_type with
   | D.DIdentTyp ((_, Some "List"), [ D.DInt _ ]) -> ()
   | _ -> fail "list annotations should use the runtime List type");
  let list_index = lower (Subscript (xs, Index (Literal (IntLit "0")))) in
  (match list_index.result with
   | D.DCallExpr (D.DDot (_, (_, Some "atIndex")), [ D.DIntLit "0" ]) -> ()
   | _ -> fail "list indexes should use the runtime atIndex operation");
  expect_exception "scoped list construction" (function Transform.Lowering.LoweringError _ -> true | _ -> false)
    (fun () ->
       Transform.Lowering.lower
         (Transform.Lowering.scoped (Transform.Lowering.context environment))
         (Lst [ Literal (IntLit "1") ]));
  let sequence_index = lower (Subscript (sequence, Index (Literal (IntLit "0")))) in
  (match sequence_index.result with
   | D.DNativeIndex (_, D.DIntLit "0") -> ()
   | _ -> fail "sequence indexes should use native Dafny indexing");
  let array_environment =
    Transform.Semantic.bind environment "array" (TGeneric (segment "array", [ int_type ]))
  in
  let array_index =
    Transform.Lowering.expression ~environment:array_environment
      (Subscript (identifier "array", Index (Literal (IntLit "0"))))
  in
  (match array_index.result with
   | D.DNativeIndex _ -> ()
   | _ -> fail "array indexes should use native Dafny indexing");
  let map_index = lower (Subscript (mapping, Index (Literal (StringLit "key")))) in
  (match map_index.result with
   | D.DNativeIndex (_, D.DStringLit "key") -> ()
   | _ -> fail "map indexes should use native Dafny indexing");
  let tuple_index = lower (Subscript (tuple, Index (Literal (IntLit "1")))) in
  (match tuple_index.result with
   | D.DTupleIndex (_, 1) -> ()
   | _ -> fail "tuple indexes should select a static tuple field");
  let unknown_index = lower (Subscript (identifier "unknown", Index (Literal (IntLit "0")))) in
  (match unknown_index.result with
   | D.DSubscript _ -> ()
   | _ -> fail "unknown collection indexes should remain explicit subscripts");
  expect_exception "dynamic tuple indexes" (function Transform.Lowering.LoweringError _ -> true | _ -> false)
    (fun () -> lower (Subscript (tuple, Index (identifier "position"))));
  let list_length = lower (Len (def_seg, xs)) in
  (match list_length.result with
   | D.DCallExpr (D.DDot (_, (_, Some "len")), []) -> ()
   | _ -> fail "list length should use the runtime len operation");
  let sequence_length = lower (Len (def_seg, sequence)) in
  (match sequence_length.result with
   | D.DLen (_, D.DIdentifier _) -> ()
   | _ -> fail "sequence length should use Dafny cardinality");
  let method_call = Call (Dot (xs, segment "method"), []) in
  let lowered_method = lower method_call in
  check int "ordinary method calls have one local prelude" 1 (List.length lowered_method.prelude);
  expect_exception "method calls are rejected in quantifiers"
    (function Transform.Lowering.LoweringError message -> has_substring message "scoped expressions" | _ -> false)
    (fun () -> ignore (lower (Forall ([ segment "k" ], method_call))));
  ignore (lower (Forall ([ segment "k" ], Call (identifier "unknown", []))));
  expect_exception "method calls are rejected in conditional branches"
    (function Transform.Lowering.LoweringError message -> has_substring message "scoped expressions" | _ -> false)
    (fun () -> ignore (lower (IfElseExp (method_call, Literal TrueLit, method_call))));
  let list_slice = lower (Subscript (xs, Slice (Some (Literal (IntLit "1")), None))) in
  check bool "list slices are hoisted into eager temporaries" true
    (match list_slice.prelude, list_slice.result with
     | [ D.DAssignLvalue (_, [ D.Local _ ], [ D.DCallExpr (D.DDot (_, (_, Some "rangeLower")), _) ]) ], D.DIdentifier _ -> true
     | _ -> false);
  let control_flow_list_slice =
    lower
      (Subscript
         (IfElseExp (xs, Literal TrueLit, xs),
          Slice (Some (Literal (IntLit "1")), None)))
  in
  check bool "list slice control flow is propagated" true control_flow_list_slice.control_flow;
  let control_flow_selector_list_slice =
    lower
      (Subscript
         (xs,
          Slice
            (Some (IfElseExp (Literal (IntLit "1"), Literal (IntLit "1"), Literal (IntLit "2"))), None)))
  in
  check bool "list slice selector control flow is propagated" true
    control_flow_selector_list_slice.control_flow;
  expect_exception "list slices are rejected in scoped expressions"
    (function Transform.Lowering.LoweringError message -> has_substring message "scoped expressions" | _ -> false)
    (fun () -> ignore (Transform.Lowering.lower
                         (Transform.Lowering.scoped (Transform.Lowering.context environment))
                         (Subscript (xs, Slice (Some (Literal (IntLit "1")), None)))));
  let nested_dictionary = lower (Dict [ Literal (StringLit "key"), method_call ]) in
  check int "nested method calls are not silently dropped" 1 (List.length nested_dictionary.prelude);
  let lowered_if_with_prelude =
    Transform.Lowering.statements ~environment
      [ IfElse (Literal TrueLit, [], [ (method_call, [ Pass ]) ], []) ]
  in
  check bool "elif condition preludes are declared before their condition" true
    (match lowered_if_with_prelude with
     | [ D.DIf (_, _, [], D.DAssignLvalue _ :: D.DIf _ :: _) ] -> true
     | _ -> false);
  let lowered_while_with_prelude =
    Transform.Lowering.statements ~environment [ While ([], method_call, [ Pass ]) ]
  in
  check bool "while condition preludes are evaluated inside the loop" true
    (match lowered_while_with_prelude with
     | [ D.DWhile ([], D.DTrue, D.DAssignLvalue _ :: D.DIf (D.DUnary (D.DNot _, _), [ D.DBreak ], [], []) :: _) ] -> true
     | _ -> false);
  let explicit_target =
    Transform.Lowering.statements ~environment
      [ Assign (None, [ Dot (xs, segment "field") ], [ Literal (IntLit "1") ]) ]
  in
  (match explicit_target with
   | [ D.DAssignLvalue (_, [ D.Field (_, (_, Some "field")) ], _) ] -> ()
   | _ -> fail "field assignments should use explicit Dafny lvalues");
  let class_environment =
    let definition : Transform.Semantic.class_definition =
      { class_name = "Box"
      ; fields =
          [ { field_name = "value"; field_type = int_type }
          ; { field_name = "apply"; field_type = TCallable (def_seg, [], int_type) }
          ]
      ; methods =
          [ { name = "run"; parameters = []; return_type = int_type
            ; kind = Transform.Semantic.Method
            } ]
      }
    in
    Transform.Semantic.add_class environment definition
    |> fun environment -> Transform.Semantic.bind environment "box" (TGeneric (segment "Box", []))
  in
  check bool "class fields resolve through the semantic environment" true
    (eqtyp
       (Transform.Semantic.infer class_environment (Dot (identifier "box", segment "value")))
       int_type);
  ignore (Transform.Semantic.infer class_environment (Dot (identifier "box", segment "missing")));
  ignore (Transform.Semantic.infer environment (Dot (identifier "ordinary", segment "field")));
  check bool "class methods resolve through the semantic environment" true
    (eqtyp
       (Transform.Semantic.infer class_environment
          (Call (Dot (identifier "box", segment "run"), [])))
       int_type);
  check bool "callable-valued fields expose their return type" true
    (eqtyp
       (Transform.Semantic.infer class_environment
          (Call (Dot (identifier "box", segment "apply"), [])))
       int_type);
  let signature : Transform.Semantic.callable_signature =
    { name = "pure"; parameters = []; return_type = int_type; kind = Transform.Semantic.PureFunction }
  in
  let function_environment = Transform.Semantic.add_function environment signature in
  let generator_signature : Transform.Semantic.callable_signature =
    { name = "generate"; parameters = []; return_type = int_type; kind = Transform.Semantic.Generator }
  in
  let constructor_signature : Transform.Semantic.callable_signature =
    { name = "construct"; parameters = []; return_type = int_type; kind = Transform.Semantic.Constructor }
  in
  let callable_environment =
    Transform.Semantic.add_function function_environment generator_signature
    |> fun environment -> Transform.Semantic.add_function environment constructor_signature
  in
  let list_consumer : Transform.Semantic.callable_signature =
    { name = "consume"; parameters = [ "items", list_type ]; return_type = int_type
    ; kind = Transform.Semantic.PureFunction }
  in
  let list_call_environment = Transform.Semantic.add_function callable_environment list_consumer in
  let empty_argument_call =
    Transform.Lowering.expression ~environment:list_call_environment
      (Call (identifier "consume", [ Lst [] ]))
  in
  check bool "call parameter types provide empty list context" true
    (match empty_argument_call.prelude with
     | [ D.DAssignLvalue (_, [ D.Local _ ], [ D.DNew (D.DIdentTyp (_, [ D.DInt _ ]), [ D.DSeqExpr [] ]) ]) ] -> true
     | _ -> false);
  check int "generator calls use a scoped temporary" 1
    (List.length
       (Transform.Lowering.expression ~environment:callable_environment
          (Call (identifier "generate", []))).prelude);
  check int "constructors remain expressions" 0
    (List.length
       (Transform.Lowering.expression ~environment:callable_environment
          (Call (identifier "construct", []))).prelude);
  check bool "callable kind is resolved" true
    (match Transform.Semantic.callable_kind function_environment (identifier "pure") with
     | Transform.Semantic.PureFunction -> true
     | _ -> false);
  check bool "unknown identifiers default to pure functions" true
    (match Transform.Semantic.callable_kind environment (identifier "unknown") with
     | Transform.Semantic.PureFunction -> true
     | _ -> false);
  check bool "non-identifier callables default to pure functions" true
    (match Transform.Semantic.callable_kind environment (Literal TrueLit) with
     | Transform.Semantic.PureFunction -> true
     | _ -> false);
  (match Transform.Semantic.normalize_type list_type with
   | TGeneric (_, [ TInt _ ]) -> ()
   | _ -> fail "list annotations should normalize to generic types");
  let all_types =
    [ TIdent (segment "Alias"); TInt def_seg; TFloat def_seg; TBool def_seg
    ; TStr def_seg; TNone def_seg; TObj def_seg; TLst (def_seg, Some int_type)
    ; TDict (def_seg, Some int_type, Some (TStr def_seg)); TSet (def_seg, Some int_type)
    ; TTuple (def_seg, Some [ int_type ]); TTuple (def_seg, None)
    ; TCallable (def_seg, [ int_type ], int_type); TType (def_seg, Some int_type)
    ; TGeneric (segment "Box", [ int_type ])
    ; TGeneric (segment "list", [ int_type ]); TGeneric (segment "seq", [ int_type ])
    ; TGeneric (segment "set", [ int_type ]); TGeneric (segment "map", [ TStr def_seg; int_type ])
    ; TGeneric (segment "array", [ int_type ]); TGeneric (segment "tuple", [ int_type; TStr def_seg ])
    ]
  in
  List.iter (fun typ -> ignore (Transform.Semantic.normalize_type typ)) all_types;
  List.iter (fun typ -> ignore (Transform.Semantic.type_name typ)) all_types;
  List.iter (fun typ -> ignore (Transform.Semantic.generic_arguments typ)) all_types;
  ignore (Transform.Semantic.lookup environment "missing");
  ignore (Transform.Semantic.lookup_function environment "missing");
  ignore (Transform.Semantic.lookup_class environment "Missing");
  ignore (Transform.Semantic.leave_scope (Transform.Semantic.enter_scope environment Transform.Semantic.ComprehensionScope));
  ignore (Transform.Semantic.leave_scope { Transform.Semantic.scopes = []; functions = []; classes = []; memberships = []; known_map_keys = []; map_aliases = []; list_aliases = []; iterated_lists = []; iterated_maps = [] });
  let replacement : Transform.Semantic.callable_signature =
    { name = "pure"; parameters = []; return_type = int_type; kind = Transform.Semantic.Constructor }
  in
  ignore (Transform.Semantic.add_function function_environment replacement);
  let replacement_class : Transform.Semantic.class_definition =
    { class_name = "Box"; fields = []; methods = [] }
  in
  ignore (Transform.Semantic.add_class class_environment replacement_class);
  List.iter
    (fun expression -> ignore (Transform.Semantic.infer environment expression))
    [ Typ list_type; Literal TrueLit; xs; Dot (xs, segment "field")
    ; UnaryExp (Not def_seg, Literal TrueLit)
    ; BinaryExp (Literal (IntLit "1"), Plus def_seg, Literal (FloatLit "1.0"))
    ; BinaryExp (Literal TrueLit, And def_seg, Literal FalseLit)
    ; Call (identifier "pure", []); Call (identifier "len", [ xs ])
    ; Call (identifier "list", [ Lst [ Literal (IntLit "1") ] ])
    ; Call (identifier "list", [])
    ; Call (identifier "set", []); Call (identifier "dict", [])
    ; Call (Dot (xs, segment "method"), []); Lst [ xs ]; Array [ xs ]; Set [ xs ]
    ; Dict [ (Literal (StringLit "k"), Literal (IntLit "1")) ]; Tuple [ xs; sequence ]
    ; Subscript (xs, Index (Literal (IntLit "0")))
    ; Subscript (mapping, Index (Literal (StringLit "k")))
    ; Subscript (tuple, Index (Literal (IntLit "1"))); Index xs
    ; Slice (Some (Literal (IntLit "0")), None); Forall ([ segment "k" ], xs)
    ; Exists ([ segment "k" ], xs); Len (def_seg, xs); Max (def_seg, xs)
    ; Old (def_seg, xs); Fresh (def_seg, xs); Lambda ([ segment "k" ], xs)
    ; IfElseExp (xs, Literal TrueLit, sequence)
    ];
  List.iter
    (fun operator ->
       ignore
         (Transform.Semantic.infer environment
            (BinaryExp (Literal (IntLit "1"), operator, Literal (IntLit "2")))))
    [ Minus def_seg; Times def_seg; Divide def_seg; Mod def_seg; EqEq def_seg
    ; NEq def_seg; Lt def_seg; LEq def_seg; Gt def_seg; GEq def_seg; Or def_seg
    ; NotIn def_seg; In def_seg; BiImpl def_seg; Implies def_seg; Explies def_seg
    ; BitOr def_seg; BitAnd def_seg ];
  ignore (Transform.Semantic.infer_literal TrueLit);
  List.iter (fun literal -> ignore (Transform.Semantic.infer_literal literal))
    [ FalseLit; IntLit "1"; FloatLit "1.0"; StringLit "s"; NoneLit ];
  ignore (Transform.Semantic.numeric_type int_type (TFloat def_seg));
  ignore (Transform.Semantic.numeric_type (TFloat def_seg) int_type);
  ignore (Transform.Semantic.numeric_type int_type int_type);
  ignore (Transform.Semantic.numeric_type (TIdent def_seg) (TIdent def_seg));
  ignore (Transform.Semantic.tuple_element 0 []);
  ignore (Transform.Semantic.tuple_element 1 [ int_type; TStr def_seg ]);
  ignore (Transform.Semantic.integer_literal (Literal (IntLit "not-an-int")));
  List.iter
    (fun target -> ignore (Transform.Semantic.type_of_target environment target))
    [ xs; Dot (xs, segment "field"); Subscript (xs, Index (Literal (IntLit "0")))
    ; Tuple [ xs; sequence ]; Literal TrueLit ];
  ignore (Transform.Semantic.infer environment (Call (Lst [], [])));
  ignore (Transform.Semantic.infer environment (Call (identifier "unknown", [])));
  ignore (Transform.Semantic.infer environment (Call (identifier "map", [])));
  ignore (Transform.Semantic.infer environment (Call (Dot (identifier "ordinary", segment "method"), [])));
  ignore (Transform.Semantic.infer environment (Call (Literal TrueLit, [])));
  ignore (Transform.Semantic.infer environment (Dict []));
  ignore (Transform.Semantic.infer environment (Subscript (sequence, Slice (None, None))));
  ignore (Transform.Semantic.infer environment (Subscript (identifier "unknown", Index (Literal (IntLit "0")))));
  ignore (Transform.Semantic.infer environment (Max (def_seg, identifier "unknown")));
  ignore (Transform.Semantic.infer environment
            (IfElseExp (Literal (IntLit "1"), Literal (IntLit "2"), Literal (IntLit "3"))));
  ignore (Transform.Semantic.infer environment
            (IfElseExp (Literal (FloatLit "1.0"), Literal (IntLit "2"), Literal (StringLit "3"))));
  ignore (Transform.Semantic.infer environment
            (IfElseExp (Literal (FloatLit "1.0"), Literal (IntLit "2"), Literal (FloatLit "3.0"))));
  ignore (Transform.Semantic.infer environment
            (IfElseExp (Literal (FloatLit "1.0"), Literal TrueLit, Literal (IntLit "3"))));
  ignore
    (Transform.Semantic.analyze
       (Program
          [ Assign (Some (Typ int_type), [ identifier "value" ], [ Literal (IntLit "1") ])
          ; Assign (Some (Typ list_type), [ identifier "xs" ], [ Lst [ Literal (IntLit "1") ] ])
          ; Assign (None, [ Dot (xs, segment "field") ], [ Literal (IntLit "1") ])
          ; IfElse (Literal TrueLit, [ Assert xs ], [ (Literal FalseLit, [ Pass ]) ], [ Exp xs ])
          ; While ([ Invariant xs ], Literal FalseLit, [ Pass ])
          ; For ([ Invariant xs ], [ segment "item" ], xs, [ Pass ])
          ; For ([], [ segment "item" ], xs, [ Break; Continue ])
          ; Break
          ; Continue
          ; Function ([], segment "local", [ segment "argument", Typ int_type ], Typ int_type, [ Return xs ])
          ]));
  List.iter (fun typ -> ignore (Transform.Lowering.type_dfy typ)) all_types;
  ignore (Transform.Todafnyast.typ_dfy (TGeneric (segment "Box", [ int_type ])));
  List.iter
    (fun typ -> expect_exception "invalid incomplete type" (function Transform.Lowering.LoweringError _ -> true | _ -> false)
       (fun () -> Transform.Lowering.type_dfy typ))
    [ TLst (def_seg, None); TSet (def_seg, None); TDict (def_seg, None, Some int_type)
    ; TDict (def_seg, Some int_type, None); TType (def_seg, None) ];
  ignore (Transform.Lowering.annotation_type (Typ int_type));
  ignore (Transform.Lowering.annotation_type (Identifier (segment "Alias")));
  expect_exception "invalid annotation" (function Transform.Lowering.LoweringError _ -> true | _ -> false)
    (fun () -> Transform.Lowering.annotation_type (Literal TrueLit));
  List.iter (fun literal -> ignore (Transform.Lowering.literal_dfy literal))
    [ TrueLit; FalseLit; IntLit "1"; FloatLit "1.0"; StringLit "s"; NoneLit ];
  List.iter (fun operator -> ignore (Transform.Lowering.unary_operator operator)) [ Not def_seg; UMinus def_seg ];
  List.iter
    (fun operator -> ignore (Transform.Lowering.binary_operator operator))
    [ NotIn def_seg; In def_seg; Plus def_seg; Minus def_seg; Times def_seg; Divide def_seg
    ; Mod def_seg; NEq def_seg; EqEq def_seg; Lt def_seg; LEq def_seg; Gt def_seg; GEq def_seg
    ; And def_seg; Or def_seg; BiImpl def_seg; Implies def_seg; Explies def_seg
    ; BitOr def_seg; BitAnd def_seg ];
  ignore (Transform.Lowering.generic_name int_type);
  ignore (Transform.Lowering.generic_arguments int_type);
  ignore (Transform.Lowering.generic_arguments list_type);
  List.iter
    (fun expression -> ignore (Transform.Lowering.expression ~environment expression))
    [ Typ (TNone def_seg); Literal (StringLit "s"); xs; Dot (xs, segment "field")
    ; BinaryExp (xs, Plus def_seg, xs); BinaryExp (xs, And def_seg, xs)
    ; BinaryExp (xs, Or def_seg, xs)
    ; UnaryExp (Not def_seg, xs); Array [ xs ]; Set [ xs ]; Tuple [ xs; sequence ]
    ; Lst [ xs ]; Dict [ (xs, sequence) ]; Tuple [ xs ]; Tuple [ xs; sequence ]
    ; Subscript (sequence, Slice (Some xs, Some sequence)); Index xs
    ; Subscript (IfElseExp (xs, Literal TrueLit, xs), Index xs)
    ; Subscript (xs, Index (IfElseExp (xs, Literal TrueLit, xs)))
    ; BinaryExp (IfElseExp (xs, Literal TrueLit, xs), Plus def_seg, xs)
    ; BinaryExp (xs, Plus def_seg, IfElseExp (xs, Literal TrueLit, xs))
    ; Dict [ (xs, IfElseExp (xs, Literal TrueLit, xs)) ]
    ; Dict [ (IfElseExp (xs, Literal TrueLit, xs), xs) ]
    ; Slice (Some xs, Some sequence); Forall ([ segment "k" ], xs)
    ; Exists ([ segment "k" ], xs); Max (def_seg, xs); Old (def_seg, xs)
    ; Fresh (def_seg, xs); Lambda ([ segment "k" ], xs)
    ; IfElseExp (xs, Literal TrueLit, sequence) ];
  List.iter
    (fun selector -> ignore (Transform.Lowering.expression ~environment (Subscript (xs, selector))))
    [ Slice (Some xs, Some sequence); Slice (Some xs, None)
    ; Slice (None, Some sequence); Slice (None, None) ];
  List.iter
    (fun selector -> ignore (Transform.Lowering.lower_selector (Transform.Lowering.context environment) selector))
    [ Index xs; Slice (Some xs, Some sequence); Slice (Some xs, None)
    ; Slice (None, Some sequence); Slice (None, None) ];
  expect_exception "type expression in value context" (function Transform.Lowering.LoweringError _ -> true | _ -> false)
    (fun () -> Transform.Lowering.expression ~environment (Typ int_type));
  ignore (Transform.Lowering.expression (Literal TrueLit));
  List.iter
    (fun specification -> ignore (Transform.Lowering.lower_spec (Transform.Lowering.context environment) specification))
    [ Pre xs; Post xs; Invariant xs; Decreases xs; Reads xs; Modifies xs ];
  expect_exception "invalid selector" (function Transform.Lowering.LoweringError _ -> true | _ -> false)
    (fun () -> Transform.Lowering.lower_selector (Transform.Lowering.context environment) (Literal TrueLit));
  let lowering_statements =
    [ Pass; Break; Exp (Call (identifier "pure", [])); Assert xs; Return xs
    ; Assign (None, [ xs ], [ Literal (IntLit "1") ])
    ; Assign (Some (Typ int_type), [ xs ], [ Literal (IntLit "2") ])
    ; IfElse (Literal TrueLit, [ Pass ], [ (Literal FalseLit, [ Pass ]) ], [ Pass ])
    ; While ([ Invariant xs ], Literal FalseLit, [ Pass ])
    ]
  in
  ignore (Transform.Lowering.statements ~environment lowering_statements);
  expect_exception "continue lowering" (function Transform.Lowering.LoweringError _ -> true | _ -> false)
    (fun () -> Transform.Lowering.statements ~environment [ Continue ]);
  expect_exception "for lowering requires loop conversion" (function Transform.Lowering.LoweringError _ -> true | _ -> false)
    (fun () -> Transform.Lowering.statements ~environment [ For ([], [], xs, []) ]);
  expect_exception "nested function lowering" (function Transform.Lowering.LoweringError _ -> true | _ -> false)
    (fun () -> Transform.Lowering.statements ~environment [ Function ([], segment "f", [], Typ int_type, []) ]);
  ignore (Transform.Lowering.lower_lvalue (Transform.Lowering.context environment) xs);
  ignore (Transform.Lowering.lower_lvalue (Transform.Lowering.context environment) (Dot (xs, segment "field")));
  ignore (Transform.Lowering.lower_lvalue (Transform.Lowering.context environment)
            (Subscript (xs, Index (Literal (IntLit "0")))));
  ignore (Transform.Lowering.lower_lvalue (Transform.Lowering.context environment) (Tuple [ xs; sequence ]));
  expect_exception "invalid lvalue" (function Transform.Lowering.LoweringError _ -> true | _ -> false)
    (fun () -> Transform.Lowering.lower_lvalue (Transform.Lowering.context environment) (Literal TrueLit));
  ignore (Transform.Lowering.lower_expression_statement (Transform.Lowering.context environment) (Call (identifier "pure", [])));
  check bool "set expression statements discard pure constructor results" true
    (Transform.Lowering.lower_expression_statement (Transform.Lowering.context environment)
       (Call (identifier "set", [])) = ([], []));
  check bool "dict expression statements discard pure constructor results" true
    (Transform.Lowering.lower_expression_statement (Transform.Lowering.context environment)
       (Call (identifier "dict", [])) = ([], []));
  ignore (Transform.Lowering.lower_expression_statement (Transform.Lowering.context environment) xs);
  ignore (Transform.Lowering.statements [ Pass ]);
  let alternative_with_prelude =
    IfElse
      (Literal TrueLit, [],
       [ (method_call, [ Pass ]) ], [])
  in
  ignore (Transform.Lowering.statements ~environment [ alternative_with_prelude ]);
  ignore (Transform.Semantic.infer environment (Subscript (identifier "unknown", Index (Literal (IntLit "0")))));
  List.iter
    (fun expression -> ignore (Transform.Convertcall.exp_calls expression))
    [ Array [ Call (identifier "array_item", []) ]
    ; Set [ Call (identifier "set_item", []) ]
    ; Dict [ (Call (identifier "dict_key", []), Call (identifier "dict_value", [])) ]
    ; Max (def_seg, Call (identifier "max_value", []))
    ; Forall ([ segment "k" ], Dict [ (identifier "k", Call (identifier "bound", [])) ])
    ; Exists ([ segment "k" ], Set [ Call (identifier "bound", []) ])
    ; Lambda ([ segment "k" ], Array [ Call (identifier "bound", []) ])
    ];
  List.iter
    (fun expression -> ignore (Transform.Convertcall.exp_calls_scoped expression))
    [ Dot (xs, segment "field"); BinaryExp (xs, Plus def_seg, xs)
    ; UnaryExp (Not def_seg, xs); Call (xs, [ xs ]); Lst [ xs ]; Array [ xs ]; Set [ xs ]
    ; Dict [ (xs, xs) ]; Tuple [ xs ]; Subscript (xs, Index xs); Index xs
    ; Slice (Some xs, None); Forall ([ segment "k" ], xs); Exists ([ segment "k" ], xs)
    ; Len (def_seg, xs); Max (def_seg, xs); Old (def_seg, xs); Fresh (def_seg, xs)
    ; Lambda ([ segment "k" ], xs); IfElseExp (xs, xs, xs) ];
  let render_expression expression =
    Transform.Emitdfy.reset ();
    Transform.Emitdfy.print_exp 0 expression
  in
  ignore (render_expression (D.DNativeIndex (D.DIdentifier (segment "value"), D.DIntLit "0")));
  ignore (render_expression (D.DTupleIndex (D.DIdentifier (segment "value"), 1)));
  Transform.Emitdfy.reset ();
  ignore (Transform.Emitdfy.print_stmt 0
            (D.DAssignLvalue (None, [ D.Local (segment "local") ], [ D.DIntLit "1" ])));
  ignore (Transform.Emitdfy.print_stmt 0
            (D.DAssignLvalue (None, [ D.Local (segment "local") ], [ D.DIntLit "2" ])));
  ignore (Transform.Emitdfy.print_stmt 0
            (D.DAssignLvalue
               (Some (D.DInt def_seg),
                [ D.Field (D.DIdentifier (segment "object"), segment "field") ],
                [ D.DIntLit "1" ])));
  ignore (Transform.Emitdfy.print_stmt 0
            (D.DAssignLvalue
               (Some (D.DInt def_seg),
                [ D.Local (segment "typed_local") ],
                [ D.DIntLit "1" ])));
  ignore (Transform.Emitdfy.print_stmt 0
            (D.DAssignLvalue
               (None,
                [ D.Index (D.DIdentifier (segment "array"), D.DIntLit "0") ],
                [ D.DIntLit "1" ])));
  ignore (Transform.Emitdfy.print_stmt 0
            (D.DAssignLvalue
               (None,
                [ D.TupleTarget [ D.Local (segment "first"); D.Local (segment "second") ] ],
               [ D.DTupleExpr [ D.DIntLit "1"; D.DIntLit "2" ] ])))

let test_phase2_semantics_and_chains () =
  let open Ast in
  let int_type = TInt def_seg in
  let identifier name = Ast.Identifier (segment name) in
  let singleton = SingletonTuple (segment ",", identifier "value") in
  (match Transform.Semantic.normalize_exp singleton with
   | Identifier (_, Some "value") -> ()
   | _ -> fail "singleton tuple normalization should return its element");
  (match Transform.Semantic.normalize_exp (Tuple [ singleton ]) with
   | Identifier (_, Some "value") -> ()
   | _ -> fail "one-element tuple normalization should be recursive");
  (match Transform.Semantic.normalize_type (TTuple (def_seg, Some [ int_type ])) with
   | TInt _ -> ()
   | _ -> fail "one-element tuple types should normalize to their element");
  (match Transform.Semantic.normalize_type (TTuple (def_seg, Some [ int_type; TStr def_seg ])) with
   | TGeneric (_, [ TInt _; TStr _ ]) -> ()
   | _ -> fail "multi-element tuple types should remain tuples");
  (match Transform.Semantic.normalize_type (TGeneric (segment "tuple", [ int_type ])) with
   | TInt _ -> ()
   | _ -> fail "generic singleton tuple types should normalize to their element");
  check bool "singleton tuple inference follows its element" true
    (match Transform.Semantic.infer Transform.Semantic.empty singleton with
     | TIdent (_, Some "value") -> true
     | _ -> false);
  check bool "singleton tuple targets follow their element" true
    (match Transform.Semantic.type_of_target Transform.Semantic.empty (Tuple [ identifier "value" ]) with
     | TIdent (_, Some "value") -> true
     | _ -> false);
  expect_exception "manual empty tuples are unsupported" (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> Transform.Semantic.normalize_exp (Tuple []));
  List.iter
    (fun expression -> ignore (Transform.Semantic.normalize_exp expression))
    [ BinaryExp (singleton, Plus def_seg, singleton)
    ; CompareChain (singleton, [ EqEq def_seg, singleton ])
    ; UnaryExp (Not def_seg, singleton)
    ; Call (singleton, [ singleton ])
    ; Lst [ singleton ]; Array [ singleton ]; Set [ singleton ]
    ; Dict [ singleton, singleton ]; Tuple [ singleton; singleton ]
    ; Subscript (singleton, Index singleton); Index singleton
    ; Slice (Some singleton, Some singleton)
    ; Forall ([ segment "bound" ], singleton); Exists ([ segment "bound" ], singleton)
    ; Len (def_seg, singleton); Max (def_seg, singleton)
    ; Old (def_seg, singleton); Fresh (def_seg, singleton)
    ; Lambda ([ segment "bound" ], singleton)
    ; IfElseExp (singleton, singleton, singleton)
    ];
  List.iter
    (fun specification -> ignore (Transform.Semantic.normalize_spec specification))
    [ Pre singleton; Post singleton; Invariant singleton; Decreases singleton
    ; Reads singleton; Modifies singleton ];
  ignore
    (Transform.Semantic.normalize_program
       (Program
          [ IfElse (singleton, [ Exp singleton ], [ (singleton, [ Assert singleton ]) ], [ Return singleton ])
          ; For ([ Pre singleton ], [ segment "item" ], singleton, [ Pass ])
          ; While ([ Post singleton ], singleton, [ Break ])
          ; Assign (Some singleton, [ singleton ], [ singleton ])
          ; Function ([], segment "nested", [ segment "argument", singleton ], singleton, [ Continue ])
          ; Pass ]));
  let environment =
    Transform.Semantic.empty
    |> fun environment -> Transform.Semantic.bind environment "first" int_type
    |> fun environment -> Transform.Semantic.bind environment "middle" int_type
    |> fun environment -> Transform.Semantic.bind environment "last" int_type
    |> fun environment -> Transform.Semantic.bind environment "values" (TLst (def_seg, Some int_type))
  in
  let chain =
    CompareChain
      ( identifier "first"
      , [ Lt def_seg, identifier "middle"; Gt def_seg, identifier "last" ] )
  in
  check bool "comparison chains infer booleans" true
    (eqtyp (Transform.Semantic.infer environment chain) (TBool def_seg));
  let lowered = Transform.Lowering.expression ~environment chain in
  check int "each chain operand is locally bound" 3
    (let rec count = function
       | D.DLet (_, _, body) -> 1 + count body
       | D.DIfElseExpr (_, when_true, when_false) -> count when_true + count when_false
       | _ -> 0
     in count lowered.result);
  check bool "comparison chains do not need eager preludes" true (lowered.prelude = []);
  Transform.Emitdfy.reset ();
  let rendered = Transform.Emitdfy.print_exp 0 lowered.result in
  check bool "comparison chains use a lazy conditional" true (has_substring rendered "if ");
  check bool "comparison chains use the false branch" true (has_substring rendered "else false");
  let initial_list_chain =
    CompareChain
      ( Call (identifier "first", [ Lst [ Literal (IntLit "1") ] ])
      , [ Lt def_seg, identifier "last" ] )
  in
  let lowered_initial_list = Transform.Lowering.expression ~environment initial_list_chain in
  check bool "initial chain setup remains in the outer prelude" true
    (List.length lowered_initial_list.prelude > 0);
  let scoped_chain =
    BinaryExp
      ( Literal TrueLit
      , And def_seg
      , CompareChain (identifier "first", [ Lt def_seg, identifier "middle" ]) )
  in
  ignore (Transform.Lowering.expression ~environment scoped_chain);
  expect_exception "empty comparison chains are unsupported"
    (function Transform.Lowering.LoweringError message -> has_substring message "at least one" | _ -> false)
    (fun () -> ignore (Transform.Lowering.expression ~environment (CompareChain (identifier "first", []))));
  let method_call = Call (Dot (identifier "values", segment "method"), []) in
  let method_chain = CompareChain (method_call, [ Lt def_seg, Literal (IntLit "1") ]) in
  expect_exception "effectful calls are rejected in scoped expressions"
    (function Transform.Lowering.LoweringError message -> has_substring message "scoped expressions" | _ -> false)
    (fun () ->
       ignore
         (Transform.Lowering.lower
            (Transform.Lowering.scoped (Transform.Lowering.context environment)) method_call));
  expect_exception "effectful calls are rejected in comparison chains"
    (function Transform.Lowering.LoweringError message -> has_substring message "effectful" | _ -> false)
    (fun () -> ignore (Transform.Lowering.expression ~environment method_chain));
  ignore (Transform.Lowering.expression ~environment (SingletonTuple (segment ",", identifier "first")));
  let effectful_argument =
    Transform.Lowering.expression ~environment
      (Call (identifier "pure", [ method_call ]))
  in
  check bool "effectful call arguments are propagated" true effectful_argument.effectful;
  let effectful_callee =
    Transform.Lowering.expression ~environment
      (Call (method_call, []))
  in
  check bool "effectful callees are propagated" true effectful_callee.effectful;
  let effectful_binary =
    Transform.Lowering.expression ~environment
      (BinaryExp (method_call, Plus def_seg, Literal (IntLit "1")))
  in
  check bool "effectful binary operands are propagated" true effectful_binary.effectful;
  let effectful_right_binary =
    Transform.Lowering.expression ~environment
      (BinaryExp (Literal (IntLit "1"), Plus def_seg, method_call))
  in
  check bool "effectful right binary operands are propagated" true effectful_right_binary.effectful;
  let effectful_subscript =
    Transform.Lowering.expression ~environment
      (Subscript (method_call, Index (Literal (IntLit "0"))))
  in
  check bool "effectful subscript operands are propagated" true effectful_subscript.effectful;
  let effectful_selector =
    Transform.Lowering.expression ~environment
      (Subscript (identifier "values", Index method_call))
  in
  check bool "effectful subscript selectors are propagated" true effectful_selector.effectful;
  let effectful_dictionary_key =
    Transform.Lowering.expression ~environment
      (Dict [ method_call, Literal (IntLit "1") ])
  in
  check bool "effectful dictionary keys are propagated" true effectful_dictionary_key.effectful;
  let method_in_final_operand =
    CompareChain
      ( identifier "first"
      , [ Lt def_seg, identifier "middle"; Gt def_seg, method_call ] )
  in
  expect_exception "effectful final chain operands are rejected"
    (function Transform.Lowering.LoweringError message -> has_substring message "effectful" | _ -> false)
    (fun () -> ignore (Transform.Lowering.expression ~environment method_in_final_operand));
  List.iter
    (fun (name, expression) ->
       expect_exception ("effectful conditional " ^ name ^ " is rejected")
         (function Transform.Lowering.LoweringError message -> has_substring message "scoped expressions" | _ -> false)
         (fun () -> ignore (Transform.Lowering.expression ~environment expression)))
    [ "true branch", IfElseExp (method_call, Literal TrueLit, Literal FalseLit)
    ; "false branch", IfElseExp (Literal TrueLit, Literal TrueLit, method_call) ];
  let effectful_condition =
    Transform.Lowering.expression ~environment
      (IfElseExp (Literal TrueLit, method_call, Literal FalseLit))
  in
  check bool "effectful conditional conditions are hoisted" true
    (match effectful_condition.prelude, effectful_condition.result with
     | _ :: _, D.DIfElseExpr (D.DIdentifier _, _, _) -> true
     | _ -> false);
  List.iter
    (fun operator ->
       expect_exception "effectful short-circuit operands are rejected"
         (function Transform.Lowering.LoweringError message -> has_substring message "scoped expressions" | _ -> false)
         (fun () -> ignore (Transform.Lowering.expression ~environment
                              (BinaryExp (Literal TrueLit, operator, method_call)))))
    [ And def_seg; Or def_seg ];
  expect_exception "chain list setup is rejected in a scoped operand"
    (function Transform.Lowering.LoweringError message -> has_substring message "comparison-chain" | _ -> false)
    (fun () ->
       ignore
         (Transform.Lowering.expression ~environment
            (CompareChain
               ( identifier "first"
               , [ Lt def_seg, identifier "middle"; Lt def_seg, Lst [ Literal (IntLit "2") ] ]))));
  let normalized_program =
    Transform.Semantic.normalize_program
      (Program
         [ Function
             ( [ Pre singleton ]
             , segment "identity"
             , [ segment "argument", Typ (TTuple (def_seg, Some [ int_type ])) ]
             , Typ (TTuple (def_seg, Some [ int_type ]))
             , [ Return singleton ] ) ])
  in
  (match normalized_program with
   | Program [ Function ([ Pre (Identifier _ ) ], _, [ (_, Typ (TInt _)) ], Typ (TInt _), [ Return (Identifier _) ]) ] -> ()
   | _ -> fail "normalization should visit function specs, parameters, returns, and bodies")

let test_phase3_collections () =
  let open Ast in
  let int_type = TInt def_seg in
  let string_type = TStr def_seg in
  let set_type = TSet (def_seg, Some int_type) in
  let map_type = TDict (def_seg, Some int_type, Some string_type) in
  let list_type = TLst (def_seg, Some int_type) in
  let sequence_type = TGeneric (segment "seq", [ int_type ]) in
  let identifier name = Ast.Identifier (segment name) in
  let values = identifier "values" in
  let mapping = identifier "mapping" in
  let list = identifier "list_value" in
  let nested_lists = identifier "nested_lists" in
  let sequence = identifier "sequence" in
  let known_map = Dict [ Literal (IntLit "1"), Literal (StringLit "value") ] in
  let env =
    Transform.Semantic.empty
    |> fun env -> Transform.Semantic.bind env "values" set_type
    |> fun env -> Transform.Semantic.bind env "mapping" map_type
    |> fun env -> Transform.Semantic.bind env "list_value" list_type
    |> fun env -> Transform.Semantic.bind env "nested_lists"
         (TGeneric (segment "list", [ list_type ]))
    |> fun env -> Transform.Semantic.bind env "sequence" sequence_type
    |> fun env -> Transform.Semantic.bind env "text" string_type
    |> fun env -> Transform.Semantic.bind env "array_value" (TGeneric (segment "array", [ int_type ]))
    |> fun env -> Transform.Semantic.bind env "tuple_value" (TTuple (def_seg, Some [ int_type; int_type ]))
  in
  let kind name expected typ =
    check bool name true (Transform.Semantic.collection_kind typ = expected)
  in
  kind "set collection classification" Transform.Semantic.SetCollection set_type;
  kind "map collection classification" Transform.Semantic.MapCollection map_type;
  kind "list collection classification" Transform.Semantic.ListCollection list_type;
  kind "sequence collection classification" Transform.Semantic.SequenceCollection sequence_type;
  kind "array collection classification" Transform.Semantic.ArrayCollection
    (TGeneric (segment "array", [ int_type ]));
  kind "tuple collection classification" Transform.Semantic.TupleCollection
    (TTuple (def_seg, Some [ int_type; string_type ]));
  kind "string collection classification" Transform.Semantic.StringCollection string_type;
  kind "unknown generic classification" Transform.Semantic.UnknownCollection
    (TGeneric (segment "custom", [ int_type ]));
  kind "unknown identifier classification" Transform.Semantic.UnknownCollection
    (TIdent (segment "Unknown"));
  kind "non-collection classification" Transform.Semantic.NonCollection int_type;
  check bool "set element type" true
    (match Transform.Semantic.collection_element_type set_type with
     | Some typ -> Transform.Semantic.compatible_types typ int_type
     | None -> false);
  List.iter
    (fun typ -> ignore (Transform.Semantic.collection_element_type typ))
    [ list_type; sequence_type; TGeneric (segment "array", [ int_type ])
    ; TTuple (def_seg, Some [ int_type; int_type ]); map_type
    ; TGeneric (segment "custom", []) ];
  check bool "empty tuple has no membership type" true
    (Option.is_none
       (Transform.Semantic.membership_type env (TTuple (def_seg, Some []))));
  check bool "map key and value types" true
    (match Transform.Semantic.map_types map_type with
     | Some (key, value) -> Transform.Semantic.compatible_types key int_type
                            && Transform.Semantic.compatible_types value string_type
     | None -> false);
  check bool "map source element is its key" true
    (match Transform.Semantic.set_source_element_type map_type with
     | Some typ -> Transform.Semantic.compatible_types typ int_type
     | None -> false);
  check bool "tuple membership has a common type" true
    (match Transform.Semantic.membership_type env (TTuple (def_seg, Some [ int_type; int_type ])) with
     | Some typ -> Transform.Semantic.compatible_types typ int_type
     | None -> false);
  ignore (Transform.Semantic.collection_element_type (TTuple (def_seg, Some [ int_type; string_type ])));
  ignore (Transform.Semantic.membership_type env (TTuple (def_seg, Some [ int_type; string_type ])));
  check bool "string membership uses strings" true
    (match Transform.Semantic.membership_type env string_type with
     | Some typ -> Transform.Semantic.compatible_types typ string_type
     | None -> false);
  check bool "unknown membership has no inferred type" true
    (Option.is_none
       (Transform.Semantic.membership_type env (TGeneric (segment "custom", []))));
  ignore (Transform.Semantic.collection_element_type (TTuple (def_seg, Some [])));
  ignore (Transform.Semantic.membership_type env sequence_type);
  ignore (Transform.Semantic.membership_type env (TGeneric (segment "array", [ int_type ])));
  ignore (Transform.Semantic.membership_type env (TGeneric (segment "set", [])));
  List.iter
    (fun typ -> ignore (Transform.Semantic.membership_type env typ))
    [ TGeneric (segment "map", []); TGeneric (segment "list", [])
    ; TGeneric (segment "seq", []); TGeneric (segment "array", []) ];
  ignore (Transform.Semantic.set_source_element_type set_type);
  ignore (Transform.Semantic.map_types int_type);
  ignore (Transform.Semantic.identifier_name (Literal TrueLit));
  ignore (Transform.Semantic.is_unknown_type (TIdent (segment "unknown")));
  check bool "concrete types compare equal" true
    (Transform.Semantic.compatible_types int_type int_type);
  ignore (Transform.Semantic.compatible_types (TIdent (segment "unknown")) int_type);
  ignore (Transform.Semantic.compatible_types int_type (TIdent (segment "unknown")));
  check bool "incompatible concrete types are rejected" false
    (Transform.Semantic.compatible_types int_type string_type);
  check bool "primitive values are hashable" true
    (List.for_all Transform.Semantic.is_hashable_type
       [ int_type; TFloat def_seg; TBool def_seg; string_type; TNone def_seg ]);
  check bool "tuples are hashable when all elements are hashable" true
    (Transform.Semantic.is_hashable_type
       (TTuple (def_seg, Some [ int_type; string_type ])));
  check bool "tuples containing lists are not hashable" false
    (Transform.Semantic.is_hashable_type
       (TTuple (def_seg, Some [ int_type; list_type ])));
  check bool "collection values are not hashable" false
    (List.exists Transform.Semantic.is_hashable_type
       [ list_type; set_type; map_type; sequence_type
       ; TGeneric (segment "array", [ int_type ]) ]);
  check bool "unknown and object values are not hashable" false
    (List.exists Transform.Semantic.is_hashable_type
       [ TIdent (segment "Unknown"); TObj def_seg
       ; TCallable (def_seg, [ int_type ], int_type) ]);
  check bool "type aliases retain hashability" true
    (Transform.Semantic.is_hashable_type (TType (def_seg, Some int_type)));
  check bool "unknown generic values are not hashable" false
    (Transform.Semantic.is_hashable_type (TGeneric (segment "custom", [ int_type ])));
  let classification_function name expression =
    Function ([], segment name, [], Typ int_type, [ Return expression ])
  in
  let classification_program =
    [ classification_function "plain" (Literal (IntLit "0"))
    ; classification_function "calls_plain" (Call (identifier "plain", []))
    ; classification_function "calls_unknown" (Call (identifier "missing", []))
    ; classification_function "calls_non_identifier"
        (Call (BinaryExp (Literal (IntLit "1"), Plus def_seg, Literal (IntLit "2")),
               [ UnaryExp (UMinus def_seg, Literal (IntLit "1")) ]))
    ; classification_function "calls_method"
        (Call (Dot (identifier "holder", segment "run"), []))
    ; classification_function "calls_classified_method" (Call (identifier "calls_method", []))
    ; classification_function "returns_type" (Typ (TNone def_seg))
    ; classification_function "returns_binary"
        (BinaryExp (Literal (IntLit "1"), Plus def_seg, Literal (IntLit "2")))
    ; classification_function "returns_binary_left_method"
        (BinaryExp (Lst [], Plus def_seg, Literal (IntLit "2")))
    ; classification_function "returns_chain"
        (CompareChain (Literal (IntLit "1"), [ (Lt def_seg, Literal (IntLit "2")) ]))
    ; classification_function "returns_chain_first_method"
        (CompareChain (Lst [], [ (Lt def_seg, Literal (IntLit "2")) ]))
    ; classification_function "returns_unary" (UnaryExp (Not def_seg, Literal TrueLit))
    ; classification_function "returns_list" (Lst [])
    ; classification_function "returns_collections"
        (Array [ Literal (IntLit "1") ])
    ; classification_function "returns_set" (Set [ Literal (IntLit "1") ])
    ; classification_function "returns_tuple" (Tuple [ Literal (IntLit "1"); Literal (IntLit "2") ])
    ; classification_function "returns_dict"
        (Dict [ Literal (IntLit "1"), Literal (IntLit "2") ])
    ; classification_function "returns_dict_key_method"
        (Dict [ Lst [], Literal (IntLit "2") ])
    ; classification_function "returns_singleton"
        (SingletonTuple (segment ",", Literal (IntLit "1")))
    ; classification_function "returns_subscript"
        (Subscript (identifier "holder", BinaryExp (Literal (IntLit "0"), Plus def_seg, Literal (IntLit "1"))))
    ; classification_function "returns_subscript_value_method"
        (Subscript (Lst [], Literal (IntLit "0")))
    ; classification_function "returns_subscript_selector_method"
        (Subscript (identifier "holder", Index (Lst [])))
    ; classification_function "returns_index" (Index (Literal (IntLit "0")))
    ; classification_function "returns_slice"
        (Slice (Some (Literal (IntLit "0")), Some (Literal (IntLit "1"))))
    ; classification_function "returns_slice_lower_method"
        (Slice (Some (Lst []), Some (Literal (IntLit "1"))))
    ; classification_function "returns_quantifier"
        (Forall ([ segment "k" ], Literal TrueLit))
    ; classification_function "returns_scope"
        (Exists ([ segment "k" ], Literal TrueLit))
    ; classification_function "returns_length" (Len (def_seg, identifier "holder"))
    ; classification_function "returns_max" (Max (def_seg, identifier "holder"))
    ; classification_function "returns_old" (Old (def_seg, identifier "holder"))
    ; classification_function "returns_fresh" (Fresh (def_seg, identifier "holder"))
    ; classification_function "returns_lambda" (Lambda ([ segment "k" ], identifier "k"))
    ; classification_function "returns_conditional"
        (IfElseExp (Literal TrueLit, Literal TrueLit, Literal FalseLit))
    ; classification_function "returns_conditional_true_method"
        (IfElseExp (Lst [], Literal TrueLit, Literal FalseLit))
    ; classification_function "returns_conditional_condition_method"
        (IfElseExp (Literal TrueLit, Lst [], Literal FalseLit))
    ; classification_function "returns_call_callee_method"
        (Call (Lst [], []))
    ; classification_function "returns_call_argument_method"
        (Call (identifier "plain", [ Lst [] ]))
    ]
  in
  let classification_environment =
    Transform.Semantic.collect_functions Transform.Semantic.empty classification_program
    |> fun environment -> Transform.Semantic.classify_functions environment classification_program
  in
  check bool "callable classification follows emitted declaration kind" true
    (match Transform.Semantic.callable_kind classification_environment (identifier "calls_classified_method") with
     | Transform.Semantic.Method -> true
     | _ -> false);
  ignore (Transform.Semantic.classify_functions Transform.Semantic.empty classification_program);
  expect_exception "incomplete set operation type"
    (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> Transform.Semantic.require_set_elements
                 (TGeneric (segment "set", [])) set_type "incomplete");
  List.iter
    (fun kind -> Transform.Semantic.require_collection kind "collection")
    [ Transform.Semantic.UnknownCollection; Transform.Semantic.ListCollection
    ; Transform.Semantic.SequenceCollection; Transform.Semantic.ArrayCollection
    ; Transform.Semantic.SetCollection; Transform.Semantic.MapCollection
    ; Transform.Semantic.TupleCollection; Transform.Semantic.StringCollection ];
  expect_exception "non-collection requirement"
    (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> Transform.Semantic.require_collection Transform.Semantic.NonCollection "collection");
  let membership_env = Transform.Semantic.add_membership env "key" "mapping" in
  ignore (Transform.Semantic.add_membership membership_env "key" "mapping");
  ignore (Transform.Semantic.add_membership env "key" "");
  ignore (Transform.Semantic.infer env (Call (identifier "setF", [ list ])));
  ignore (Transform.Semantic.infer env (Call (identifier "dictF", [])));
  List.iter
    (fun literal ->
       check bool "literal map keys are recognized" true
         (Option.is_some (Transform.Semantic.literal_key (Literal literal))))
    [ IntLit "1"; FloatLit "1.0"; StringLit "key"; TrueLit; FalseLit; NoneLit ];
  check bool "non-literal map keys are unknown" true
    (Option.is_none (Transform.Semantic.literal_key values));
  ignore (Transform.Semantic.known_literal_key env known_map (Literal TrueLit));
  ignore (Transform.Semantic.known_literal_key env known_map values);
  ignore
    (Transform.Semantic.known_literal_key env
       (Dict [ values, Literal (StringLit "value") ]) (Literal (IntLit "1")));
  ignore (Transform.Semantic.known_literal_key env (Literal TrueLit) (Literal TrueLit));
  let lower expression = Transform.Lowering.expression ~environment:env expression in
  (match (lower (Call (identifier "set", []))).result with
   | D.DSetExpr [] -> ()
   | _ -> fail "set() should lower to an empty set value");
  (match (lower (Call (identifier "setF", []))).result with
   | D.DSetExpr [] -> ()
   | _ -> fail "setF() should share set() lowering");
  (match (lower (Call (identifier "dict", []))).result with
   | D.DMapExpr [] -> ()
   | _ -> fail "dict() should lower to an empty map value");
  (match (lower (Call (identifier "dictF", []))).result with
   | D.DMapExpr [] -> ()
   | _ -> fail "dictF() should share dict() lowering");
  (match (lower (Call (identifier "set", [ list ]))).result with
   | D.DCallExpr (D.DIdentifier (_, Some "setFromSeq"), [ D.DDot (_, (_, Some "lst")) ]) -> ()
   | _ -> fail "set(list) should use the sequence conversion helper");
  check bool "set conversion keeps its resolved type" true
    (Transform.Semantic.collection_kind
       (lower (Call (identifier "set", [ list ]))).resolved_type
     = Transform.Semantic.SetCollection);
  (match (lower (Call (identifier "set", [ sequence ]))).result with
   | D.DCallExpr (D.DIdentifier (_, Some "setFromSeq"), [ D.DIdentifier _ ]) -> ()
   | _ -> fail "set(sequence) should use the sequence conversion helper");
  (match (lower (Call (identifier "set", [ mapping ]))).result with
   | D.DMapKeys (D.DIdentifier (_, Some "mapping")) -> ()
   | _ -> fail "set(map) should use map keys");
  (match (lower (Call (identifier "set", [ values ]))).result with
   | D.DIdentifier (_, Some "values") -> ()
   | _ -> fail "set(set) should preserve the set value");
  (match (lower (Dict [ Literal (IntLit "1"), Literal (StringLit "first")
                    ; Literal (IntLit "1"), Literal (StringLit "last") ])).result with
   | D.DMapUpdate
       (D.DMapUpdate (D.DMapExpr [], D.DIntLit "1", D.DStringLit "first"),
        D.DIntLit "1", D.DStringLit "last") -> ()
   | _ -> fail "dictionary displays should apply updates left to right");
  let set_union = lower (BinaryExp (values, BitOr def_seg, values)) in
  let set_intersection = lower (BinaryExp (values, BitAnd def_seg, values)) in
  let set_difference = lower (BinaryExp (values, Minus def_seg, values)) in
  check bool "set union lowering" true
    (match set_union.result with D.DBinary (_, D.DSetUnion _, _) -> true | _ -> false);
  check bool "set intersection lowering" true
    (match set_intersection.result with D.DBinary (_, D.DSetIntersection _, _) -> true | _ -> false);
  check bool "set difference lowering" true
    (match set_difference.result with D.DBinary (_, D.DSetDifference _, _) -> true | _ -> false);
  check bool "set algebra inference" true
    (Transform.Semantic.collection_kind set_union.resolved_type = Transform.Semantic.SetCollection);
  check bool "set length uses cardinality" true
    (match (lower (Len (def_seg, values))).result with D.DLen (_, _) -> true | _ -> false);
  check bool "map length uses cardinality" true
    (match (lower (Len (def_seg, mapping))).result with D.DLen (_, _) -> true | _ -> false);
  let list_membership = lower (BinaryExp (Literal (IntLit "1"), In def_seg, list)) in
  check bool "list membership uses the runtime contains function" true
    (match list_membership.result with
     | D.DCallExpr (D.DDot (D.DIdentifier (_, Some "list_value"), (_, Some "contains")),
                    [ D.DIntLit "1" ]) -> true
     | _ -> false);
  let list_nonmembership = lower (BinaryExp (Literal (IntLit "1"), NotIn def_seg, list)) in
  check bool "list non-membership negates the runtime contains function" true
    (match list_nonmembership.result with
     | D.DUnary (D.DNot _, D.DCallExpr (D.DDot (_, (_, Some "contains")), _)) -> true
     | _ -> false);
  expect_exception "untyped empty list literals are rejected"
    (function Transform.Lowering.LoweringError message -> has_substring message "concrete list" | _ -> false)
    (fun () -> ignore (Transform.Lowering.expression ~environment:env (Lst [])));
  expect_exception "empty lists need a concrete element type"
    (function Transform.Lowering.LoweringError message -> has_substring message "concrete element" | _ -> false)
    (fun () -> ignore (Transform.Lowering.expression ~environment:env
                         ~expected_type:(TGeneric (segment "list", [])) (Lst [])));
  expect_exception "empty lists need a list expected type"
    (function Transform.Lowering.LoweringError message -> has_substring message "list type" | _ -> false)
    (fun () -> ignore (Transform.Lowering.expression ~environment:env
                         ~expected_type:int_type (Lst [])));
  let typed_empty_assignment =
    Transform.Lowering.statements ~environment:env
      [ Assign (Some (Typ list_type), [ identifier "empty_list" ], [ Lst [] ]) ]
  in
  check bool "typed empty list assignments construct a typed runtime List" true
    (match typed_empty_assignment with
     | [ D.DAssignLvalue
           ( None
           , [ D.Local _ ]
           , [ D.DNew (D.DIdentTyp (_, [ D.DInt _ ]), [ D.DSeqExpr [] ]) ] )
       ; D.DAssignLvalue
           ( Some (D.DIdentTyp (_, [ D.DInt _ ]))
           , [ D.Local (_, Some "empty_list") ]
           , [ D.DIdentifier _ ] ) ] -> true
     | _ -> false);
  let typed_empty_return =
    Transform.Lowering.expression ~environment:env ~expected_type:list_type (Lst [])
  in
  check bool "expected return types propagate into empty list literals" true
    (match typed_empty_return.prelude with
     | [ D.DAssignLvalue (_, [ D.Local _ ], [ D.DNew (D.DIdentTyp (_, [ D.DInt _ ]), [ D.DSeqExpr [] ]) ]) ] -> true
     | _ -> false);
  (match (Transform.Lowering.expression ~environment:env
           (Subscript (known_map, Index (Literal (IntLit "1"))))).result with
   | D.DNativeIndex (D.DMapUpdate _, D.DIntLit "1") -> ()
   | _ -> fail "map lookup should remain native map indexing");
  let map_update =
    Transform.Lowering.statements ~environment:env
      [ Assign (None, [ Subscript (mapping, Index (Literal (IntLit "1"))) ],
                [ Literal (StringLit "updated") ]) ]
  in
  (match map_update with
   | [ D.DAssignLvalue (_, [ D.Local (_, Some "mapping") ],
                       [ D.DMapUpdate (D.DIdentifier (_, Some "mapping"), D.DIntLit "1", D.DStringLit "updated") ]) ] -> ()
   | _ -> fail "map assignment should lower to a functional update");
  let effectful_map_update =
    Transform.Lowering.statements ~environment:env
      [ Assign
          ( None
          , [ Subscript (mapping, Index (Call (Dot (list, segment "pop"), []))) ]
          , [ Call (Dot (list, segment "pop"), []) ] ) ]
  in
  check bool "map updates evaluate values before keys" true
    (match effectful_map_update with
     | [ D.DAssignLvalue (_, [ D.Local (_, Some "lowered_1") ], [_])
       ; D.DAssignLvalue (_, [ D.Local (_, Some "lowered_2") ], [_])
       ; D.DAssignLvalue
           (_, [ D.Local (_, Some "mapping") ],
            [ D.DMapUpdate
                ( D.DIdentifier (_, Some "mapping")
                , D.DIdentifier (_, Some "lowered_2")
                , D.DIdentifier (_, Some "lowered_1") ) ]) ] -> true
     | _ -> false);
  let ordinary_binary = lower (BinaryExp (list, Plus def_seg, list)) in
  check bool "non-set binary operations keep their original operator" true
    (match ordinary_binary.result with D.DBinary (_, D.DPlus _, _) -> true | _ -> false);
  ignore (Transform.Lowering.collection_binary_operator env list (Plus def_seg) list);
  ignore (Transform.Lowering.collection_binary_operator env list (Minus def_seg) list);
  expect_exception "List indexed assignments are rejected by lowering"
    (function Transform.Lowering.LoweringError message -> has_substring message "List" | _ -> false)
    (fun () -> ignore (Transform.Lowering.statements ~environment:env
                         [ Assign (None, [ Subscript (list, Index (Literal (IntLit "0"))) ],
                                   [ Literal (IntLit "1") ]) ]));
  expect_exception "List indexed assignments are rejected semantically"
    (function Transform.Semantic.SemanticError message -> has_substring message "List" | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements env
                         [ Assign (None, [ Subscript (list, Index (Literal (IntLit "0"))) ],
                                   [ Literal (IntLit "1") ]) ]));
  List.iter
    (fun expression ->
       expect_exception "unsupported set constructor lowering"
         (function Transform.Lowering.LoweringError _ -> true | _ -> false)
         (fun () -> ignore (Transform.Lowering.expression ~environment:env expression)))
    [ Call (identifier "set", [ Literal (IntLit "1") ])
    ; Call (identifier "set", [ list; sequence ])
    ; Call (identifier "dict", [ Literal (IntLit "1") ]) ];
  expect_exception "unsupported collection loop lowering"
    (function Transform.Lowering.LoweringError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Lowering.statements ~environment:env
                         [ For ([], [ segment "item" ], identifier "text", [ Pass ]) ]));
  expect_exception "non-map functional update lowering"
    (function Transform.Lowering.LoweringError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Lowering.lower_map_assignment
                         (Transform.Lowering.context env) (segment "list_value")
                         (Literal (IntLit "0")) (Literal (IntLit "1"))));
  expect_exception "direct map updates are rejected in an iterated context"
    (function Transform.Lowering.LoweringError message -> has_substring message "while iterating" | _ -> false)
    (fun () -> ignore (Transform.Lowering.lower_map_assignment
                         { (Transform.Lowering.context env) with iterated_maps = [ "other_map"; "mapping" ] }
                         (segment "mapping") (Literal (IntLit "0"))
                         (Literal (StringLit "value"))));
  ignore (Transform.Lowering.lower_lvalue (Transform.Lowering.context env)
            (Subscript (sequence, Index (Literal (IntLit "0")))));
  ignore (Transform.Lowering.lower_assignment (Transform.Lowering.context env) None
            [ Subscript (identifier "unknown", Index (Literal (IntLit "0"))) ]
            [ Literal (IntLit "1") ]);
  expect_exception "List indexed assignments are rejected directly"
    (function Transform.Lowering.LoweringError message -> has_substring message "List" | _ -> false)
    (fun () -> ignore (Transform.Lowering.lower_assignment (Transform.Lowering.context env)
                         (Some (Typ int_type))
                         [ Subscript (list, Index (Literal (IntLit "0"))) ]
                         [ Literal (IntLit "1") ]));
  expect_exception "unknown collection loop lowering"
    (function Transform.Lowering.LoweringError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Lowering.lower_for (Transform.Lowering.context env) []
                         [ segment "item" ] (identifier "unknown") [ Pass ]));
  expect_exception "missing collection loop target"
    (function Transform.Lowering.LoweringError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Lowering.lower_for (Transform.Lowering.context env) []
                         [] values [ Pass ]));
  let specs =
    [ Pre (Literal TrueLit); Post (Literal TrueLit); Invariant (Literal TrueLit)
    ; Decreases (Literal (IntLit "1")); Reads (Literal TrueLit); Modifies (Literal TrueLit) ]
  in
  ignore (Transform.Semantic.validate_specs env specs);
  let set_loop =
    Transform.Lowering.statements ~environment:env
      [ For ([], [ segment "item" ], values, [ Assert (BinaryExp (identifier "item", In def_seg, values)) ]) ]
  in
  let map_loop =
    Transform.Lowering.statements ~environment:env
      [ For ([], [ segment "key" ], mapping
           , [ Assert (BinaryExp (identifier "key", In def_seg, mapping)) ]) ]
  in
  let indexed_loop_specs =
    [ Invariant (Literal TrueLit); Decreases (Literal (IntLit "1")) ]
  in
  let list_loop =
    Transform.Lowering.statements ~environment:env
      [ For (indexed_loop_specs, [ segment "item" ], list, [ Pass ]) ]
  in
  let sequence_loop =
    Transform.Lowering.statements ~environment:env
      [ For ([], [ segment "item" ], sequence, [ Pass ]) ]
  in
  let has_choose statements =
    List.exists (function
      | D.DWhile (_, _, D.DAssignSuchThat _ :: _) -> true
      | _ -> false) statements
  in
  check bool "set loops choose from a remaining set" true (has_choose set_loop);
  check bool "map loops choose from a snapshot of keys" true (has_choose map_loop);
  check bool "map loops snapshot their key set" true
    (List.exists
       (fun statement -> has_substring (Transform.Emitdfy.print_stmt 0 statement) ".Keys")
       map_loop);
  check bool "list loops use indexed lowering" true
    (has_substring (Transform.Emitdfy.print_stmt 0 (List.hd list_loop)) "lowered_");
  check bool "sequence loops use indexed lowering" true
    (has_substring (Transform.Emitdfy.print_stmt 0 (List.hd sequence_loop)) "lowered_");
  ignore (Transform.Lowering.lower_for (Transform.Lowering.context env) indexed_loop_specs
            [ segment "item" ] list [ Pass ]);
  ignore (Transform.Lowering.lower_for (Transform.Lowering.context env) []
            [ segment "item" ] sequence [ Pass ]);
  let list_continue_loop =
    Transform.Lowering.statements ~environment:env
      [ For ([], [ segment "item" ], list, [ Continue ]) ]
  in
  check bool "list loop bookkeeping precedes continue" true
    (match List.rev list_continue_loop with
     | D.DWhile (_, _, [ D.DAssignLvalue _; D.DAssignLvalue _; D.DContinue ]) :: _ -> true
     | _ -> false);
  expect_exception "list mutation during iteration is rejected by lowering"
    (function Transform.Lowering.LoweringError message -> has_substring message "while iterating" | _ -> false)
    (fun () -> ignore (Transform.Lowering.statements ~environment:env
                         [ For ([], [ segment "item" ], list
                              , [ Exp (Call (Dot (list, segment "append"),
                                             [ Literal (IntLit "3") ])) ]) ]));
  let list_alias = identifier "list_alias" in
  let list_alias_env =
    Transform.Semantic.validate_statements env
      [ Assign (None, [ list_alias ], [ list ]) ]
  in
  expect_exception "list aliases are protected during iteration"
    (function Transform.Lowering.LoweringError message -> has_substring message "while iterating" | _ -> false)
    (fun () -> ignore (Transform.Lowering.statements ~environment:list_alias_env
                         [ For ([], [ segment "item" ], list
                              , [ Exp (Call (Dot (list_alias, segment "append"),
                             [ Literal (IntLit "3") ])) ]) ]));
  let map_alias = identifier "map_alias" in
  let map_alias_env =
    Transform.Semantic.validate_statements env
      [ Assign (None, [ map_alias ], [ mapping ]) ]
  in
  expect_exception "map mutation during iteration is rejected by lowering"
    (function Transform.Lowering.LoweringError message -> has_substring message "while iterating" | _ -> false)
    (fun () -> ignore (Transform.Lowering.statements ~environment:env
                         [ For ([], [ segment "key" ], mapping
                              , [ Assign (None, [ Subscript (mapping, Index (Literal (IntLit "3"))) ],
                                          [ Literal (StringLit "value") ]) ]) ]));
  expect_exception "map aliases are protected during iteration by lowering"
    (function Transform.Lowering.LoweringError message -> has_substring message "while iterating" | _ -> false)
    (fun () -> ignore (Transform.Lowering.statements ~environment:map_alias_env
                         [ For ([], [ segment "key" ], map_alias
                              , [ Assign (None, [ Subscript (mapping, Index (Literal (IntLit "3"))) ],
                                          [ Literal (StringLit "value") ]) ]) ]));
  List.iter
    (fun specification ->
       expect_exception "invalid loop specifications are rejected"
         (function Transform.Semantic.SemanticError _ -> true | _ -> false)
         (fun () -> ignore (Transform.Semantic.validate_statements env
                              [ For ([ specification ], [ segment "item" ], list, [ Pass ]) ]));
       expect_exception "invalid loop specifications cannot be lowered"
         (function Transform.Lowering.LoweringError _ -> true | _ -> false)
         (fun () -> ignore (Transform.Lowering.lower_for (Transform.Lowering.context env)
                              [ specification ] [ segment "item" ] list [ Pass ]));
       expect_exception "invalid while specifications are rejected"
         (function Transform.Semantic.SemanticError _ -> true | _ -> false)
         (fun () -> ignore (Transform.Semantic.validate_statements env
                              [ While ([ specification ], Literal FalseLit, [ Pass ]) ])))
    [ Pre (Literal TrueLit); Post (Literal TrueLit); Reads (Literal TrueLit); Modifies (Literal TrueLit) ];
  let last_set_statement =
    match List.rev set_loop with
    | statement :: _ -> statement
    | [] -> fail "set loop lowering should produce statements"
  in
  check bool "set loops remove their chosen item" true
    (has_substring
       (Transform.Emitdfy.print_stmt 0 last_set_statement)
       "- {item}");
  let valid_map_program =
    [ Assign (Some (Typ map_type), [ mapping ], [ known_map ])
    ; Assert (Subscript (mapping, Index (Literal (IntLit "1"))))
    ; Assign (None, [ Subscript (mapping, Index (Literal (IntLit "2"))) ],
              [ Literal (StringLit "another") ])
    ; Assign (None, [ Subscript (mapping, Index (Literal (IntLit "2"))) ],
              [ Literal (StringLit "again") ]) ]
  in
  ignore (Transform.Semantic.validate_statements Transform.Semantic.empty valid_map_program);
  ignore
    (Transform.Semantic.validate_statements env
       [ For ([], [ segment "item" ], list, [ Pass ])
       ; For ([], [ segment "item" ], sequence, [ Pass ])
       ]);
  ignore
    (Transform.Semantic.validate_statements env
       [ For ([], [ segment "key" ], mapping
            , [ Assert (Subscript (mapping, Index (identifier "key"))) ]) ]);
  let keyed_env = Transform.Semantic.bind env "key" int_type in
  let membership_condition = BinaryExp (identifier "key", In def_seg, mapping) in
  let map_lookup = Subscript (mapping, Index (identifier "key")) in
  ignore
    (Transform.Semantic.validate_statements keyed_env
       [ IfElse (membership_condition, [ Assert map_lookup ], [], [ Pass ]) ]);
  expect_exception "map membership proofs do not leak into else branches"
    (function Transform.Semantic.SemanticError message -> has_substring message "membership precondition" | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements keyed_env
                         [ IfElse (membership_condition, [ Pass ], [], [ Assert map_lookup ]) ]));
  expect_exception "map membership proofs do not leak into elif branches"
    (function Transform.Semantic.SemanticError message -> has_substring message "membership precondition" | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements keyed_env
                         [ IfElse (membership_condition, [ Pass ],
                                   [ (Literal TrueLit, [ Assert map_lookup ]) ], [ Pass ]) ]));
  expect_exception "map membership proofs do not leak after conditionals"
    (function Transform.Semantic.SemanticError message -> has_substring message "membership precondition" | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements keyed_env
                         [ IfElse (membership_condition, [ Pass ], [], [ Pass ])
                         ; Assert map_lookup ]));
  expect_exception "multi-target list iteration is rejected semantically"
    (function Transform.Semantic.SemanticError message -> has_substring message "one loop target" | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements env
                         [ For ([], [ segment "first"; segment "second" ], list, [ Pass ]) ]));
  expect_exception "set constructor rejects unhashable source elements"
    (function Transform.Semantic.SemanticError message -> has_substring message "hashable" | _ -> false)
    (fun () -> Transform.Semantic.validate_exp env (Call (identifier "set", [ nested_lists ])));
  expect_exception "list mutation during iteration is rejected semantically"
    (function Transform.Semantic.SemanticError message -> has_substring message "while iterating" | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements env
                         [ For ([], [ segment "item" ], list
                              , [ Exp (Call (Dot (list, segment "append"),
                                             [ Literal (IntLit "3") ])) ]) ]));
  expect_exception "list aliases are rejected semantically during iteration"
    (function Transform.Semantic.SemanticError message -> has_substring message "while iterating" | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements list_alias_env
                         [ For ([], [ segment "item" ], list
                              , [ Exp (Call (Dot (list_alias, segment "append"),
                                             [ Literal (IntLit "3") ])) ]) ]));
  expect_exception "map mutation during iteration is rejected semantically"
    (function Transform.Semantic.SemanticError message -> has_substring message "while iterating" | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements env
                         [ For ([], [ segment "key" ], mapping
                              , [ Assign (None, [ Subscript (mapping, Index (Literal (IntLit "3"))) ],
                                          [ Literal (StringLit "value") ]) ]) ]));
  expect_exception "map aliases are protected during iteration semantically"
    (function Transform.Semantic.SemanticError message -> has_substring message "while iterating" | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements map_alias_env
                         [ For ([], [ segment "key" ], map_alias
                              , [ Assign (None, [ Subscript (mapping, Index (Literal (IntLit "3"))) ],
                                          [ Literal (StringLit "value") ]) ]) ]));
  let nested_list_type = TGeneric (segment "list", [ list_type ]) in
  let nested_loop_environment =
    Transform.Semantic.empty
    |> fun env -> Transform.Semantic.bind env "xs" nested_list_type
    |> fun env -> Transform.Semantic.bind env "ys" nested_list_type
  in
  let nested_shadowing_loop =
    For
      ( []
      , [ segment "x" ]
      , identifier "xs"
      , [ For
            ( []
            , [ segment "xs" ]
            , identifier "ys"
            , [ Exp (Call (Dot (identifier "xs", segment "append"), [ Literal (IntLit "1") ])) ] ) ] )
  in
  ignore (Transform.Semantic.validate_statements nested_loop_environment [ nested_shadowing_loop ]);
  ignore (Transform.Lowering.statements ~environment:nested_loop_environment [ nested_shadowing_loop ]);
  let nested_map_type = TGeneric (segment "map", [ int_type; string_type ]) in
  let nested_map_environment =
    Transform.Semantic.empty
    |> fun env -> Transform.Semantic.bind env "outer_mapping"
         (TGeneric (segment "map", [ int_type; nested_map_type ]))
    |> fun env -> Transform.Semantic.bind env "other_mapping"
         (TGeneric (segment "map", [ int_type; nested_map_type ]))
  in
  let nested_map_loop =
    For
      ( []
      , [ segment "outer_key" ]
      , identifier "outer_mapping"
      , [ For ([], [ segment "outer_mapping" ], identifier "other_mapping", [ Pass ]) ] )
  in
  ignore (Transform.Semantic.validate_statements nested_map_environment [ nested_map_loop ]);
  ignore (Transform.Lowering.statements ~environment:nested_map_environment [ nested_map_loop ]);
  let untyped_list_env =
    Transform.Semantic.bind Transform.Semantic.empty "untyped_list"
      (TGeneric (segment "list", []))
  in
  expect_exception "set constructor requires a concrete source element type"
    (function Transform.Semantic.SemanticError message -> has_substring message "concrete source" | _ -> false)
    (fun () -> Transform.Semantic.validate_exp untyped_list_env
                 (Call (identifier "set", [ identifier "untyped_list" ])));
  ignore
    (Transform.Semantic.validate_statements untyped_list_env
       [ For ([], [ segment "item" ], identifier "untyped_list", [ Pass ]) ]);
  let lookup_function =
    Function
      ( [ Pre (BinaryExp (identifier "key", In def_seg, identifier "mapping")) ]
      , segment "lookup"
      , [ segment "mapping", Typ map_type; segment "key", Typ int_type ]
      , Typ string_type
      , [ Return (Subscript (identifier "mapping", Index (identifier "key"))) ] )
  in
  ignore (Transform.Semantic.analyze (Program [ lookup_function ]));
  ignore
    (Transform.Semantic.validate_statements
       (Transform.Semantic.bind Transform.Semantic.empty "values" set_type)
       [ For ([], [ segment "item" ], values, [ Pass ]) ]);
  ignore
    (Transform.Semantic.validate_statements env
       [ Assert (UnaryExp (Not def_seg, Literal FalseLit))
       ; Assert (CompareChain (Literal (IntLit "1"), [ (Lt def_seg, Literal (IntLit "2")) ]))
       ; Assert (Array [ Literal (IntLit "1") ])
       ; Assert (Set [ Literal (IntLit "1") ])
       ; Assert (Dict [ (Literal (IntLit "1"), Literal (StringLit "value")) ])
       ; Assert (Tuple [ Literal (IntLit "1"); Literal (IntLit "2") ])
       ; Assert (SingletonTuple (segment ",", Literal (IntLit "1")))
       ; Assert (Index (Literal (IntLit "1")))
       ; Assert (Slice (Some (Literal (IntLit "0")), None))
       ; Assert (Forall ([ segment "bound" ], BinaryExp (identifier "bound", EqEq def_seg, identifier "bound")))
       ; Assert (Exists ([ segment "bound" ], BinaryExp (identifier "bound", EqEq def_seg, identifier "bound")))
       ; Assert (Len (def_seg, values))
       ; Assert (Max (def_seg, values))
       ; Assert (Old (def_seg, values))
       ; Assert (Fresh (def_seg, values))
       ; Assert (Lambda ([ segment "bound" ], identifier "bound"))
       ; Assert (IfElseExp (Literal TrueLit, Literal TrueLit, Literal FalseLit))
       ; Assert (Subscript (sequence, Index (Literal (IntLit "0"))))
       ; Assert (Subscript (identifier "unknown", Index (Literal (IntLit "0"))))
       ; Assert (Subscript (sequence, Slice (None, None)))
       ; Assert (Subscript (known_map, Index (Literal (IntLit "1"))))
       ; Assert (BinaryExp (values, EqEq def_seg, values))
       ; Assert (BinaryExp (mapping, EqEq def_seg, mapping))
       ; Assert (BinaryExp (Literal (IntLit "1"), NotIn def_seg, list))
       ; Assert (BinaryExp (values, Minus def_seg, values))
       ; Assert (BinaryExp (values, BitOr def_seg, values))
       ; Assert (BinaryExp (values, BitAnd def_seg, values))
       ; Exp (Call (identifier "setF", []))
       ; Exp (Call (identifier "setF", [ list ]))
       ; Exp (Call (identifier "setF", [ sequence ]))
       ; Exp (Call (identifier "setF", [ values ]))
       ; Exp (Call (identifier "setF", [ mapping ]))
       ; Exp (Call (identifier "dictF", []))
       ; Exp (Call (identifier "map", []))
       ; Exp (Call (identifier "ordinary", []))
       ; Exp (Call (Dot (values, segment "contains"), [ Literal (IntLit "1") ]))
       ; Exp (BinaryExp (Literal (IntLit "1"), Minus def_seg, Literal (IntLit "2")))
       ; Exp (BinaryExp (Literal (IntLit "1"), Plus def_seg, Literal (IntLit "2")))
       ; Exp (BinaryExp (Literal TrueLit, EqEq def_seg, Literal TrueLit))
       ; Pass; Break; Continue ]);
  List.iter
    (fun expression -> Transform.Semantic.validate_exp env expression)
    [ Dot (values, segment "field")
    ; BinaryExp (values, NEq def_seg, values)
    ; Tuple [ Literal (IntLit "1"); Literal (IntLit "2") ]
    ; Array [ Literal (IntLit "1"); Literal (IntLit "2") ]
    ; Set [ Literal (IntLit "1"); Literal (IntLit "2") ]
    ; Dict [ (Literal (IntLit "1"), Literal (StringLit "a")); (Literal (IntLit "2"), Literal (StringLit "b")) ]
    ; Subscript (identifier "array_value", Index (Literal (IntLit "0")))
    ; Subscript (identifier "tuple_value", Index (Literal (IntLit "0")))
    ; Subscript (identifier "list_value", Slice (None, None))
    ; Subscript (identifier "array_value", Slice (None, None))
    ; Subscript (identifier "tuple_value", Slice (None, None))
    ; Subscript (identifier "unknown", Slice (Some (Literal (IntLit "0")), Some (Literal (IntLit "1"))))
    ; Forall ([ segment "bound" ], Literal TrueLit)
    ; Exists ([ segment "bound" ], Literal TrueLit)
    ; Len (def_seg, list)
    ; Max (def_seg, list)
    ; Old (def_seg, list)
    ; Fresh (def_seg, list)
    ; Lambda ([ segment "bound" ], identifier "bound")
    ; IfElseExp (Literal TrueLit, Literal TrueLit, Literal FalseLit) ];
  List.iter
    (fun expression -> Transform.Semantic.validate_exp env expression)
    [ Lst []; Array []; Set []; Dict []
    ; Subscript (identifier "array_value", Index (Literal (IntLit "0")))
    ; Subscript (identifier "tuple_value", Index (Literal (IntLit "0"))) ];
  ignore
    (Transform.Semantic.validate_statements env
       [ IfElse (Literal TrueLit, [ Pass ], [ (Literal FalseLit, [ Exp values ]) ], [ Pass ])
       ; While ([ Invariant (Literal TrueLit); Decreases (Literal (IntLit "1")) ], Literal FalseLit, [ Pass ])
       ; Assign (None, [ Dot (values, segment "field") ], [ Literal (IntLit "1") ])
       ; Assign (None, [ Tuple [ identifier "left"; identifier "right" ] ],
                 [ Tuple [ Literal (IntLit "1"); Literal (IntLit "2") ] ])
       ; Assign (None, [ Subscript (identifier "unknown", Index (Literal (IntLit "0"))) ],
                 [ Literal (IntLit "1") ])
       ; Return values ]);
  ignore (Transform.Semantic.validate_target env (Tuple [ identifier "left"; identifier "right" ]));
  ignore (Transform.Semantic.validate_target env
            (Subscript (identifier "unknown", Slice (None, None))));
  ignore (Transform.Semantic.validate_target env
            (Subscript (identifier "unknown", Index (Literal (IntLit "0")))));
  expect_exception "List indexed target validation is rejected"
    (function Transform.Semantic.SemanticError message -> has_substring message "List" | _ -> false)
    (fun () -> Transform.Semantic.validate_target env
                (Subscript (list, Index (Literal (IntLit "0")))));
  ignore
    (Transform.Semantic.assume_membership env
       (CompareChain (identifier "key", [ (In def_seg, mapping) ])));
  let unrelated_list_aliases =
    { env with list_aliases = [ ("other", "different") ] }
  in
  check (Alcotest.list Alcotest.string) "unrelated list aliases are excluded" [ "list" ]
    (Transform.Semantic.list_aliases_for unrelated_list_aliases "list");
  let aliases_to_rebind =
    { env with list_aliases = [ ("alias", "source"); ("other", "target") ] }
  in
  ignore (Transform.Semantic.bind aliases_to_rebind "alias" list_type);
  ignore (Transform.Semantic.bind aliases_to_rebind "source" list_type);
  let unrelated_map_aliases =
    { env with map_aliases = [ ("other_map", "different_map") ] }
  in
  check (Alcotest.list Alcotest.string) "unrelated map aliases are excluded" [ "mapping" ]
    (Transform.Semantic.map_aliases_for unrelated_map_aliases "mapping");
  let map_aliases_to_rebind =
    { env with map_aliases = [ ("alias_map", "source_map"); ("other_map", "target_map") ] }
  in
  ignore (Transform.Semantic.bind map_aliases_to_rebind "alias_map" map_type);
  ignore (Transform.Semantic.bind map_aliases_to_rebind "source_map" map_type);
  ignore (Transform.Semantic.known_literal_key env known_map (identifier "dynamic"));
  ignore (Transform.Semantic.add_membership env "" "");
  ignore (Transform.Semantic.add_map_key env "mapping" values);
  ignore (Transform.Semantic.bind_value env "alias" map_type mapping);
  ignore (Transform.Semantic.bind (Transform.Semantic.bind_value env "alias" map_type mapping)
            "alias" map_type);
  expect_exception "invalid assignment target" (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements env
                         [ Assign (None, [ Literal TrueLit ], [ Literal TrueLit ]) ]));
  expect_exception "invalid subscript target" (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements env
                         [ Assign (None, [ Subscript (values, Literal TrueLit) ], [ Literal (IntLit "1") ]) ]));
  expect_exception "non-indexable value" (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements env
                         [ Assert (Subscript (Literal TrueLit, Index (Literal (IntLit "0")))) ]));
  expect_exception "unsupported slice" (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements env
                         [ Assert (Subscript (values, Slice (None, None))) ]));
  let semantic_error name expression =
    expect_exception name
      (function Transform.Semantic.SemanticError _ -> true | _ -> false)
      (fun () -> ignore (Transform.Semantic.validate_statements env [ Assert expression ]))
  in
  let unhashable_set_env =
    Transform.Semantic.bind env "bad_set"
      (TGeneric (segment "set", [ list_type ]))
  in
  semantic_error "incompatible set member" (BinaryExp (Lst [ Literal (IntLit "1") ], In def_seg, values));
  expect_exception "unhashable set membership operand"
    (function Transform.Semantic.SemanticError message -> has_substring message "hashable" | _ -> false)
    (fun () -> Transform.Semantic.validate_exp unhashable_set_env
                 (BinaryExp (Lst [ Literal (IntLit "1") ], In def_seg, identifier "bad_set")));
  semantic_error "incompatible membership" (BinaryExp (Literal (StringLit "bad"), In def_seg, values));
  semantic_error "non-collection membership" (BinaryExp (Literal (IntLit "1"), In def_seg, Literal TrueLit));
  semantic_error "set algebra needs sets" (BinaryExp (list, BitOr def_seg, values));
  let string_set_env = Transform.Semantic.bind env "other_set" (TSet (def_seg, Some string_type)) in
  expect_exception "incompatible set algebra elements"
    (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements string_set_env
                         [ Assert (BinaryExp (values, BitAnd def_seg, identifier "other_set")) ]));
  ignore (Transform.Semantic.validate_binary env (Literal (IntLit "1")) (Minus def_seg)
            (Literal (IntLit "2")));
  expect_exception "set difference requires a set on the left"
    (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_binary env (Literal (IntLit "1"))
                         (Minus def_seg) values));
  expect_exception "incompatible collection elements"
    (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> Transform.Semantic.validate_exp env
                 (Lst [ Literal (IntLit "1"); Literal (StringLit "bad") ]));
  expect_exception "incompatible dictionary keys"
    (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> Transform.Semantic.validate_exp env
                 (Dict [ (Literal (IntLit "1"), Literal (StringLit "ok"));
                         (Literal (StringLit "bad"), Literal (StringLit "ok")) ]));
  expect_exception "incompatible dictionary values"
    (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> Transform.Semantic.validate_exp env
                 (Dict [ (Literal (IntLit "1"), Literal (StringLit "ok"));
                         (Literal (IntLit "2"), Literal (IntLit "bad")) ]));
  expect_exception "unhashable set literal elements"
    (function Transform.Semantic.SemanticError message -> has_substring message "hashable" | _ -> false)
    (fun () -> Transform.Semantic.validate_exp env
                 (Set [ Lst [ Literal (IntLit "1") ] ]));
  expect_exception "unhashable dictionary keys"
    (function Transform.Semantic.SemanticError message -> has_substring message "hashable" | _ -> false)
    (fun () -> Transform.Semantic.validate_exp env
                 (Dict [ Lst [ Literal (IntLit "1") ], Literal (StringLit "value") ]));
  semantic_error "set and map equality" (BinaryExp (values, EqEq def_seg, mapping));
  expect_exception "incompatible map equality keys"
    (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_equality
                         (TGeneric (segment "map", [ int_type; string_type ]))
                         (TGeneric (segment "map", [ string_type; string_type ]))));
  expect_exception "incomplete map equality"
    (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_equality
                         (TGeneric (segment "map", [])) (TGeneric (segment "map", []))));
  expect_exception "incomplete set equality"
    (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_equality
                         (TGeneric (segment "set", [])) (TGeneric (segment "set", []))));
  ignore (Transform.Semantic.validate_equality
            (TGeneric (segment "map", [])) map_type);
  ignore (Transform.Semantic.validate_equality
            (TGeneric (segment "set", [])) set_type);
  let incomplete_map_env =
    Transform.Semantic.bind Transform.Semantic.empty "incomplete_map"
      (TGeneric (segment "map", []))
  in
  expect_exception "incomplete map update"
    (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements incomplete_map_env
                         [ Assign
                             ( None
                             , [ Subscript (identifier "incomplete_map",
                                             Index (Literal (IntLit "1"))) ]
                             , [ Literal (StringLit "value") ] ) ]));
  expect_exception "incomplete map lookup"
    (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements incomplete_map_env
                         [ Assert (Subscript (identifier "incomplete_map",
                                              Index (Literal (IntLit "1")))) ]));
  ignore (Transform.Semantic.validate_equality int_type int_type);
  ignore (Transform.Semantic.validate_equality map_type map_type);
  ignore (Transform.Semantic.validate_map_lookup env (identifier "unknown") (Literal (IntLit "1")));
  ignore (Transform.Semantic.validate_map_lookup env list (Literal (IntLit "0")));
  expect_exception "reverse set/map equality"
    (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_equality map_type set_type));
  List.iter
    (fun (left, right) ->
       expect_exception "mixed collection equality"
         (function Transform.Semantic.SemanticError _ -> true | _ -> false)
         (fun () -> ignore (Transform.Semantic.validate_equality left right)))
    [ set_type, int_type; int_type, set_type; map_type, int_type; int_type, map_type ];
  semantic_error "map lookup needs a proof" (Subscript (mapping, Index (Literal (IntLit "1"))));
  ignore (Transform.Semantic.validate_exp env
            (BinaryExp (values, EqEq def_seg, Call (identifier "set", []))));
  ignore (Transform.Semantic.validate_exp env
            (BinaryExp (mapping, EqEq def_seg, Call (identifier "dict", []))));
  semantic_error "map lookup key type" (Subscript (mapping, Index (Literal TrueLit)));
  semantic_error "set constructor arity" (Call (identifier "set", [ list; sequence ]));
  semantic_error "set constructor source" (Call (identifier "set", [ Literal (IntLit "1") ]));
  semantic_error "set constructor array" (Call (identifier "set", [ identifier "array_value" ]));
  semantic_error "set constructor tuple" (Call (identifier "set", [ identifier "tuple_value" ]));
  semantic_error "set constructor string" (Call (identifier "set", [ identifier "text" ]));
  semantic_error "set constructor unknown" (Call (identifier "set", [ identifier "unknown" ]));
  semantic_error "dict constructor arguments" (Call (identifier "dict", [ Literal (IntLit "1") ]));
  semantic_error "map constructor arguments" (Call (identifier "map", [ Literal (IntLit "1") ]));
  semantic_error "set mutation" (Call (Dot (values, segment "add"), [ Literal (IntLit "1") ]));
  semantic_error "map mutation" (Call (Dot (mapping, segment "setdefault"), [ Literal (IntLit "1") ]));
  List.iter
    (fun method_name ->
       semantic_error ("set mutation " ^ method_name)
         (Call (Dot (values, segment method_name), [ Literal (IntLit "1") ])))
    [ "remove"; "discard"; "pop"; "clear"; "update"; "intersection_update"; "difference_update"; "symmetric_difference_update" ];
  List.iter
    (fun method_name ->
       semantic_error ("map mutation " ^ method_name)
         (Call (Dot (mapping, segment method_name), [ Literal (IntLit "1") ])))
    [ "pop"; "popitem"; "update"; "clear" ];
  Transform.Semantic.validate_exp env (Call (Literal TrueLit, []));
  let class_env =
    let definition : Transform.Semantic.class_definition =
      { class_name = "Holder"
      ; fields = [ { field_name = "mapping"; field_type = map_type } ]
      ; methods = [] }
    in
    Transform.Semantic.add_class env definition
    |> fun env -> Transform.Semantic.bind env "holder" (TGeneric (segment "Holder", []))
  in
  expect_exception "map field update" (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements class_env
                         [ Assign (None, [ Subscript (Dot (identifier "holder", segment "mapping"), Index (Literal (IntLit "1"))) ],
                                   [ Literal (StringLit "value") ]) ]));
  expect_exception "nested map update" (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements
                         (Transform.Semantic.validate_statements Transform.Semantic.empty
                            [ Assign (Some (Typ map_type), [ mapping ], [ known_map ]) ])
                         [ Assign (None, [ Subscript (Subscript (mapping, Index (Literal (IntLit "1"))),
                                                   Index (Literal (IntLit "2"))) ],
                                   [ Literal (StringLit "value") ]) ]));
  let alias_program =
    [ Assign (None, [ identifier "alias" ], [ mapping ])
    ; Assign (None, [ Subscript (identifier "alias", Index (Literal (IntLit "1"))) ],
              [ Literal (StringLit "value") ]) ]
  in
  expect_exception "map alias update" (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements env alias_program));
  expect_exception "multi-target set loop" (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements env
                         [ For ([], [ segment "first"; segment "second" ], values, [ Pass ]) ]));
  expect_exception "unsupported string loop" (function Transform.Semantic.SemanticError _ -> true | _ -> false)
    (fun () -> ignore (Transform.Semantic.validate_statements env
                         [ For ([], [ segment "character" ], identifier "text", [ Pass ]) ]));
  List.iter
    (fun iterable ->
       expect_exception "unsupported typed loop" (function Transform.Semantic.SemanticError _ -> true | _ -> false)
         (fun () -> ignore (Transform.Semantic.validate_statements env
                              [ For ([], [ segment "item" ], iterable, [ Pass ]) ])))
    [ identifier "array_value"; identifier "tuple_value"; identifier "unknown"; Literal TrueLit ]

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
    (Option.is_none
       (Transform.Generics.convert_typvar
          (identifier "T") (Call (identifier "Other", [ Literal (StringLit "Other") ]))));
  check bool "non-call generic rhs is ignored" true
    (Option.is_none (Transform.Generics.convert_typvar (identifier "T") (Literal TrueLit)));
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
  let mutation =
    Call (Dot (Identifier (segment "xs"), segment "append"), [ Literal (IntLit "1") ])
  in
  let other_call = Call (Dot (Identifier (segment "other"), segment "copy"), []) in
  let pure = Identifier (segment "value") in
  let check_modifies name expression =
    check bool name true (Transform.Todafnyast.expression_modifies [ "xs" ] expression)
  in
  let check_not_modifies name expression =
    check bool name false (Transform.Todafnyast.expression_modifies [ "xs" ] expression)
  in
  check_modifies "direct list mutation" mutation;
  check_not_modifies "non-mutating method call" other_call;
  check_not_modifies "non-mutating list method call"
    (Call (Dot (Identifier (segment "xs"), segment "copy"), []));
  check_modifies "nested call argument" (Call (pure, [ mutation ]));
  check_modifies "nested call callee" (Call (other_call, [ mutation ]));
  check_modifies "modifying generic callee"
    (Call (Call (pure, [ mutation ]), []));
  check bool "method call with a non-identifier argument is not inferred to modify" false
    (Transform.Todafnyast.expression_modifies ~method_names:[ "method" ] [ "xs" ]
       (Call (Identifier (segment "method"), [ Literal (IntLit "1") ])));
  check_modifies "nested dot expression" (Dot (mutation, segment "field"));
  check_modifies "binary expression left" (BinaryExp (mutation, Plus def_seg, pure));
  check_modifies "binary expression right" (BinaryExp (pure, Plus def_seg, mutation));
  check_modifies "comparison chain first" (CompareChain (mutation, []));
  check_modifies "comparison chain operand"
    (CompareChain (pure, [ (EqEq def_seg, pure); (EqEq def_seg, mutation) ]));
  check_modifies "unary expression" (UnaryExp (Not def_seg, mutation));
  check_modifies "list expression" (Lst [ mutation ]);
  check_modifies "array expression" (Array [ mutation ]);
  check_modifies "set expression" (Set [ mutation ]);
  check_modifies "tuple expression" (Tuple [ mutation ]);
  check_modifies "dictionary expression" (Dict [ (pure, mutation) ]);
  check_modifies "dictionary key" (Dict [ (mutation, pure) ]);
  check_modifies "singleton tuple expression" (SingletonTuple (segment ",", mutation));
  check_modifies "index expression" (Index mutation);
  check_modifies "subscript value" (Subscript (mutation, Index pure));
  check_modifies "subscript selector" (Subscript (pure, Index mutation));
  check_modifies "slice lower bound" (Slice (Some mutation, Some pure));
  check_modifies "slice upper bound" (Slice (Some pure, Some mutation));
  check_modifies "forall expression" (Forall ([ segment "item" ], mutation));
  check_modifies "exists expression" (Exists ([ segment "item" ], mutation));
  check_modifies "lambda expression" (Lambda ([ segment "item" ], mutation));
  check_modifies "length expression" (Len (def_seg, mutation));
  check_modifies "max expression" (Max (def_seg, mutation));
  check_modifies "old expression" (Old (def_seg, mutation));
  check_modifies "fresh expression" (Fresh (def_seg, mutation));
  check_modifies "conditional true expression"
    (IfElseExp (mutation, pure, pure));
  check_modifies "conditional condition expression"
    (IfElseExp (pure, mutation, pure));
  check_modifies "conditional false expression"
    (IfElseExp (pure, pure, mutation));
  check_not_modifies "type expression" (Typ (TInt def_seg));
  check_not_modifies "literal expression" (Literal TrueLit);
  check_not_modifies "identifier expression" pure;
  let check_statement name statement =
    check bool name true (Transform.Todafnyast.statement_modifies [ "xs" ] statement)
  in
  check_statement "assignment mutation"
    (Assign (None, [ pure ], [ mutation ]));
  check_statement "assignment target mutation"
    (Assign (None, [ mutation ], [ pure ]));
  check_statement "if condition mutation"
    (IfElse (mutation, [ Pass ], [], [ Pass ]));
  check_statement "if first branch mutation"
    (IfElse (pure, [ Exp mutation ], [], [ Pass ]));
  check_statement "if alternative condition mutation"
    (IfElse (pure, [ Pass ], [ (mutation, [ Pass ]) ], [ Pass ]));
  check_statement "if alternative mutation"
    (IfElse (pure, [ Pass ], [ (pure, [ Exp mutation ]) ], [ Pass ]));
  check_statement "if final mutation"
    (IfElse (pure, [ Pass ], [ (pure, [ Pass ]) ], [ Exp mutation ]));
  check_statement "while mutation"
    (While ([], pure, [ Exp mutation ]));
  check_statement "while condition mutation"
    (While ([], mutation, [ Pass ]));
  check_statement "for mutation"
    (For ([], [ segment "item" ], pure, [ Exp mutation ]));
  check_statement "for iterable mutation"
    (For ([], [ segment "item" ], mutation, [ Pass ]));
  check_statement "nested function mutation"
    (Function ([], segment "nested", [], Typ (TNone def_seg), [ Exp mutation ]));
  check_statement "return mutation" (Return mutation);
  check_statement "assert mutation" (Assert mutation);
  check_statement "expression mutation" (Exp mutation);
  List.iter
    (fun statement ->
       check bool "non-mutating control statement" false
         (Transform.Todafnyast.statement_modifies [ "xs" ] statement))
    [ Break; Continue; Pass ];
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
  expect_exception "dict with untyped value" (function Transform.Todafnyast.ToDfyError _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.typ_dfy (TDict (def_seg, Some int_typ, None)));
  expect_exception "untyped type" (function Transform.Todafnyast.ToDfyError _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.typ_dfy (TType (def_seg, None)));
  let x = identifier "x" in
  let y = identifier "y" in
  let expressions =
    [ x
    ; Dot (x, segment "field")
    ; BinaryExp (x, Plus def_seg, Literal (IntLit "1"))
    ; CompareChain (x, [ Lt def_seg, y; Gt def_seg, x ])
    ; CompareChain (x, [])
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
    ; SingletonTuple (segment ",", x)
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
    ; BiImpl def_seg; Implies def_seg; Explies def_seg
    ; BitOr def_seg; BitAnd def_seg ]
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
  check bool "continue statement conversion" true
    (match Transform.Todafnyast.stmt_dfy Continue with D.DContinue -> true | _ -> false);
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
  check bool "non-type alias rhs is ignored" true
    (Option.is_none (Transform.Todafnyast.convert_typsyn (Identifier (segment "NotAType")) (Literal TrueLit)));
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
  let function_method =
    Function
      ([ Pre (Literal TrueLit) ], segment "method", [ param ], Typ int_typ,
       [ Return (Call (Dot (Identifier (segment "arg"), segment "run"), [])) ])
  in
  let function_body =
    Function
      ([], segment "body", [], Typ int_typ,
       [ Assert (Literal TrueLit); Return (Literal (IntLit "1")) ])
  in
  let list_function =
    Function
      ([], segment "list_function",
       [ segment "values", Typ (TLst (def_seg, Some int_typ)) ], Typ int_typ,
       [ Return (Subscript (identifier "values", Index (Literal (IntLit "0")))) ])
  in
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
  ignore (Transform.Todafnyast.func_dfy [] Pass);
  ignore (Transform.Todafnyast.func_dfy [] function_body);
  expect_exception "unequal top-level declaration" (function Transform.Todafnyast.ToDfyError _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.toplevel_dfy [] (Assign (None, [ x; y ], [ Typ int_typ ])));
  ignore (Transform.Todafnyast.prog_dfy
            (Program [ function_return
                     ; function_method
                     ; function_exp
                     ; function_body
                     ; function_pass
                     ; list_function
                     ; Assign (None, [ x ], [ Typ int_typ ]) ]))

let test_emitter_paths_and_sourcemaps () =
  let ds name = segment name in
  let id name = D.DIdentifier (ds name) in
  let operators =
    [ D.DNotIn def_seg; D.DIn def_seg; D.DEq def_seg; D.DNEq def_seg
    ; D.DPlus def_seg; D.DMinus def_seg; D.DTimes def_seg; D.DDivide def_seg
    ; D.DMod def_seg; D.DLt def_seg; D.DLEq def_seg; D.DGt def_seg
    ; D.DGEq def_seg; D.DAnd def_seg; D.DOr def_seg; D.DNot def_seg
    ; D.DBiImpl def_seg; D.DImplies def_seg; D.DExplies def_seg
    ; D.DSetUnion def_seg; D.DSetIntersection def_seg; D.DSetDifference def_seg
    ; D.DSetSubset def_seg
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
  check string "array type rendering" "array<int>"
    (render_type (D.DArray (def_seg, D.DInt def_seg)));
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
    ; D.DNew (D.DIdentTyp (ds "List", [ D.DInt def_seg ]), [ D.DSeqExpr [ id "x" ] ])
    ; D.DArrayExpr [ id "x" ]; D.DSetExpr [ id "x" ]
    ; D.DMapExpr [ (id "x", D.DIntLit "1") ]; D.DMapKeys (id "mapping")
    ; D.DMapUpdate (D.DMapExpr [], D.DIntLit "1", D.DIntLit "2")
    ; D.DSubscript (id "x", D.DIndex (D.DIntLit "0"))
    ; D.DIndex (id "x"); D.DSlice (Some (D.DIntLit "1"), Some (D.DIntLit "2"))
    ; D.DSlice (Some (D.DIntLit "1"), None); D.DSlice (None, Some (D.DIntLit "2"))
    ; D.DSlice (None, None); D.DForall ([ ds "k" ], D.DTrue)
    ; D.DExists ([ ds "k" ], D.DFalse); D.DLen (def_seg, id "x")
    ; D.DOld (def_seg, id "x"); D.DFresh (def_seg, id "x")
    ; D.DLambda ([ (ds "x", D.DVoid) ], [], id "x")
    ; D.DLet (ds "bound", D.DIntLit "1", id "bound")
    ; D.DIfElseExpr (D.DTrue, D.DIntLit "1", D.DIntLit "2")
    ; D.DTupleExpr [ id "x"; id "y" ]
    ]
  in
  Transform.Emitdfy.reset ();
  check string "newline concatenation" "first\nsecond"
    (Transform.Emitdfy.newline_concat (fun value -> value) [ "first"; "second" ]);
  check bool "lookup searches past the first declaration" true
    (Transform.Emitdfy.lookup "f" "x" [ ("g", "y"); ("f", "x") ]);
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
  check string "new expression rendering" "new List<int>([x])"
    (render_exp (D.DNew (D.DIdentTyp (ds "List", [ D.DInt def_seg ]), [ D.DSeqExpr [ id "x" ] ])));
  check string "sequence rendering" "[x, y]"
    (render_exp (D.DSeqExpr [ id "x"; id "y" ]));
  check string "array rendering" "[x, y]"
    (render_exp (D.DArrayExpr [ id "x"; id "y" ]));
  check string "set rendering" "{x, y}"
    (render_exp (D.DSetExpr [ id "x"; id "y" ]));
  check string "map rendering" "map[x := 1, y := 2]"
    (render_exp (D.DMapExpr [ (id "x", D.DIntLit "1"); (id "y", D.DIntLit "2") ]));
  check string "map keys rendering" "mapping.Keys"
    (render_exp (D.DMapKeys (id "mapping")));
  check string "map update rendering" "map[][1 := 2]"
    (render_exp (D.DMapUpdate (D.DMapExpr [], D.DIntLit "1", D.DIntLit "2")));
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
  check string "exists rendering" "exists k :: false"
    (render_exp (D.DExists ([ ds "k" ], D.DFalse)));
  check string "length rendering" "|x|" (render_exp (D.DLen (def_seg, id "x")));
  check string "old rendering" "old(x)" (render_exp (D.DOld (def_seg, id "x")));
  check string "fresh rendering" "fresh(x)" (render_exp (D.DFresh (def_seg, id "x")));
  check string "lambda rendering" "(x) => x"
    (render_exp (D.DLambda ([ (ds "x", D.DVoid) ], [], id "x")));
  check string "lambda specification rendering" "(x)requires true => x"
    (render_exp
       (D.DLambda ([ (ds "x", D.DVoid) ], [ D.DRequires D.DTrue ], id "x")));
  check string "let rendering" "(var bound := 1; bound)"
    (render_exp (D.DLet (ds "bound", D.DIntLit "1", id "bound")));
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
  check string "typed declaration without initializer" "var z: int;"
    (Transform.Emitdfy.print_stmt 0
       (D.DAssign (Some (D.DInt def_seg), [ ds "z" ], [])));
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
  check string "continue rendering" "continue;"
    (Transform.Emitdfy.print_stmt 0 D.DContinue);
  check string "call statement rendering" "f(1);"
    (Transform.Emitdfy.print_stmt 0 (D.DCallStmt (id "f", [ D.DIntLit "1" ])));
  check string "return statement rendering" "return 1;"
    (Transform.Emitdfy.print_stmt 0 (D.DReturn [ D.DIntLit "1" ]));
  check string "choose assignment rendering" "var item: int :| (item in remaining);"
    (Transform.Emitdfy.print_stmt 0
       (D.DAssignSuchThat (Some (D.DInt def_seg), D.Local (ds "item"),
                           D.DBinary (id "item", D.DIn def_seg, id "remaining"))));
  check string "choose field assignment rendering" "var object.field :| true;"
    (Transform.Emitdfy.print_stmt 0
       (D.DAssignSuchThat (None, D.Field (id "object", ds "field"), D.DTrue)));
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
    [ D.DEmptyStmt; D.DAssume D.DTrue; D.DAssert D.DTrue; D.DBreak; D.DContinue
    ; D.DAssign (None, [], []); D.DAssign (None, [ ds "x" ], [])
    ; D.DAssign (Some (D.DInt def_seg), [ ds "y" ], [ D.DIntLit "1" ])
    ; D.DCallStmt (id "f", [ D.DIntLit "1" ])
    ; D.DIf (D.DTrue, [ D.DAssert D.DTrue ], [ (D.DFalse, [ D.DBreak ]) ], [ D.DEmptyStmt ])
    ; D.DWhile ([ D.DInvariant D.DTrue ], D.DTrue, [ D.DBreak ])
    ; D.DReturn [ D.DIntLit "1" ]
    ; D.DAssignSuchThat (Some (D.DInt def_seg), D.Local (ds "item"),
                         D.DBinary (id "item", D.DIn def_seg, id "remaining"))
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
    ; D.DMeth ([], ds "void_m", [], [], [ D.DVoid ], None)
    ]
  in
  let source = Transform.Emitdfy.print_prog (D.DProg ("", top_levels)) in
  check bool "emitter prints declarations" true (String.length source > 0);
  let source_again = Transform.Emitdfy.print_prog (D.DProg ("", top_levels)) in
  check string "emitter is repeatable" source source_again;
  let mapping = ref [ ((2, 3), segment "nearest"); ((1, 1), segment "other") ] in
  check string "nearest source map entry" "nearest" (seg_val (Transform.Emitdfy.nearest_seg !mapping 2 3));
  check string "nearest source map with one entry" "nearest"
    (seg_val (Transform.Emitdfy.nearest_seg [ ((2, 3), segment "nearest") ] 2 3));
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
  Run.Report.report "verifier finished with 1 verified, 0 errors\n";
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
  let read_attempts = ref 0 in
  let read_with_interrupt _ _ _ _ =
    incr read_attempts;
    if !read_attempts = 1 then
      raise (Unix.Unix_error (Unix.EINTR, "read", ""))
    else 0
  in
  check int "interrupted reads are retried" 0
    (Run.Pipeline.read_available read_with_interrupt Unix.stdin (Bytes.create 1));
  check int "interrupted read is retried once" 2 !read_attempts;
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
                  ; test_case "phase 2 parser forms" `Quick test_phase2_parser_forms
                  ; test_case "phase 3 collection parser forms" `Quick test_phase3_collection_parser_forms
                  ; test_case "AST utilities" `Quick test_ast_utilities
                  ; test_case "AST serializers and subtyping" `Quick test_ast_serializers_and_subtyping ])
    ; ("transforms", [ test_case "call state reset" `Quick test_transform_state_resets
                      ; test_case "emitter state reset" `Quick test_emitter_resets_state
                      ; test_case "Dafny 4 function syntax" `Quick test_dafny4_function_syntax
                      ; test_case "list conversion paths" `Quick test_convertlist_paths
                      ; test_case "list statement paths" `Quick test_convertlist_statement_paths
                      ; test_case "call and for conversion" `Quick test_convertcall_and_convertfor_paths
                      ; test_case "for statement paths" `Quick test_convertfor_statement_paths
                      ; test_case "semantic lowering paths" `Quick test_semantic_lowering_paths
                      ; test_case "phase 2 semantics and chains" `Quick test_phase2_semantics_and_chains
                      ; test_case "phase 3 collections" `Quick test_phase3_collections
                      ; test_case "generic conversion" `Quick test_generics_paths
                      ; test_case "call expression paths" `Quick test_convertcall_expression_paths
                      ; test_case "Dafny AST conversion" `Quick test_todafnyast_paths
                      ; test_case "emitter and source maps" `Quick test_emitter_paths_and_sourcemaps ])
    ; ("report", [ test_case "report parsing" `Quick test_report_paths ])
    ; ("pipeline", [ test_case "injected commands and cleanup" `Quick test_pipeline_injects_commands_and_cleans_files
                    ; test_case "failure and artifact paths" `Quick test_pipeline_failure_and_artifact_paths
                    ; test_case "system and exception paths" `Quick test_pipeline_system_and_exception_paths ])
    ]
