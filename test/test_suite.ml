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
   | Pyparse.Parser.ParseError _ -> ())

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
  check string "segment update" "new" (seg_val (update_seg_val (segment "old") (Some "new")));
  (try
     ignore (idlst_to_id [ Literal (IntLit "1") ]);
     fail "invalid identifier lists should raise"
   with
   | Pyparse.Astpy.PyAstError _ -> ())

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
  expect_exception "invalid subscript" (function Ast.PyAstError _ -> true | _ -> false)
    (fun () -> Transform.Convertlist.exp_lst (Subscript (xs, Literal (IntLit "1"))))

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
  let _, rewritten_quantifier = Transform.Convertcall.exp_calls quantifier in
  (match rewritten_quantifier with
   | Forall (_, Identifier (_, Some "tempcall_1")) -> ()
   | _ -> fail "calls in quantifiers should be rewritten");
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
   | Program [ Assign _; Assign _; Assign _; While (specs, _, body) ] ->
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
   | Program (Assign _ :: Function (specs, _, _, _, _) :: _) ->
     check bool "function spec call assignment" true (List.length specs > 0)
   | _ -> fail "function call conversion should preserve function");
  ignore (Transform.Convertcall.prog (Program [ IfElse (nested, [ Exp nested ], [ (nested, [ Pass ]) ], [ Return nested ]) ]))

let test_convertcall_expression_paths () =
  let open Ast in
  let x = identifier "x" in
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
    ]
  in
  List.iter (fun expression -> ignore (Transform.Convertcall.exp_calls expression)) expressions;
  let statements =
    [ Pass; Break; Continue; Exp x; Assign (None, [ x ], [ x ])
    ; IfElse (x, [ Pass ], [ (x, [ Break ]) ], [ Continue ])
    ; Return x; Assert x; While ([ Pre x ], x, [ Pass ])
    ; For ([ Post x ], [ segment "i" ], x, [ Pass ])
    ; Function ([ Reads x ], segment "f", [], Typ (TInt def_seg), [ Pass ])
    ]
  in
  List.iter (fun statement -> ignore (Transform.Convertcall.stmt_calls statement)) statements

let test_generics_paths () =
  let open Ast in
  let type_var name = Call (identifier "TypeVar", [ Literal (StringLit name) ]) in
  let program =
    Program
      [ Assign (None, [ identifier "T" ], [ type_var "T" ])
      ; Assign (None, [ identifier "S" ], [ identifier "T" ])
      ; Assign (None, [ identifier "value" ], [ Literal (IntLit "1") ])
      ]
  in
  (match Transform.Generics.prog program with
   | Program [ Assign (_, [ Identifier (_, Some "value") ], _) ], [ "T"; "S" ] -> ()
   | _ -> fail "TypeVar declarations should become generic parameters");
  expect_exception "constrained TypeVar" (function Ast.PyAstError _ -> true | _ -> false)
    (fun () -> Transform.Generics.prog (Program [ Assign (None, [ identifier "T" ], [ Call (identifier "TypeVar", [ Literal (StringLit "T"); Literal (IntLit "1") ]) ]) ]));
  expect_exception "unequal generic assignment" (function Ast.PyAstError _ -> true | _ -> false)
    (fun () -> Transform.Generics.generics (Assign (None, [ identifier "x" ], [])))

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
  expect_exception "function statement" (function Assert_failure _ -> true | _ -> false)
    (fun () -> Transform.Todafnyast.stmt_dfy (Function ([], segment "f", [], Typ int_typ, [])));
  Transform.Todafnyast.reset ();
  (match Transform.Todafnyast.convert_typsyn (Identifier (segment "Alias")) (Typ int_typ) with
   | Some (D.DTypSynonym _) -> ()
   | _ -> fail "a type assignment should become a Dafny type synonym");
  (match Transform.Todafnyast.convert_typsyn (Identifier (segment "Alias2")) (Identifier (segment "Alias")) with
   | Some (D.DTypSynonym _) -> ()
   | _ -> fail "a type alias should resolve to a known synonym");
  check bool "None is not a top-level declaration" false
    (Transform.Todafnyast.is_toplevel (Assign (None, [ x ], [ Typ (TNone def_seg) ])));
  check bool "typed assignment is a top-level declaration" true
    (Transform.Todafnyast.is_toplevel (Assign (None, [ x ], [ Typ int_typ ])));
  check bool "function is top-level" true
    (Transform.Todafnyast.is_toplevel (Function ([], segment "f", [], Typ int_typ, [])));
  let function_return = Function ([], segment "f", [ param ], Typ int_typ, [ Return x ]) in
  let function_exp = Function ([], segment "g", [], Typ int_typ, [ Exp x ]) in
  let function_pass = Function ([], segment "h", [], Typ int_typ, [ Pass ]) in
  ignore (Transform.Todafnyast.func_dfy [] function_return);
  ignore (Transform.Todafnyast.func_dfy [] function_exp);
  ignore (Transform.Todafnyast.func_dfy [] function_pass);
  ignore (Transform.Todafnyast.toplevel_dfy [] function_return);
  ignore (Transform.Todafnyast.toplevel_dfy [] (Assign (None, [ x ], [ Typ int_typ ])));
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
  ignore (Transform.Emitdfy.print_rets 0 []);
  ignore (Transform.Emitdfy.print_rets 0 [ D.DVoid ]);
  ignore (Transform.Emitdfy.print_rets 0 [ D.DInt def_seg ]);
  let top_levels =
    [ D.DTypSynonym (ds "Alias", Some (D.DInt def_seg))
    ; D.DFuncMeth ([ D.DEnsures D.DTrue ], ds "f", [ "T" ], [], D.DInt def_seg, Some D.DTrue)
    ; D.DMeth ([ D.DRequires D.DTrue ], ds "m", [], [ (ds "x", D.DInt def_seg) ], [ D.DInt def_seg ], Some [ D.DReturn [ D.DIntLit "1" ] ])
    ]
  in
  let source = Transform.Emitdfy.print_prog (D.DProg ("", top_levels)) in
  check bool "emitter prints declarations" true (String.length source > 0);
  let source_again = Transform.Emitdfy.print_prog (D.DProg ("", top_levels)) in
  check string "emitter is repeatable" source source_again;
  let mapping = ref [ ((2, 3), segment "nearest"); ((1, 1), segment "other") ] in
  check string "nearest source map entry" "nearest" (seg_val (Transform.Emitdfy.nearest_seg !mapping 2 3));
  check string "empty source map fallback" "Line: 0  Column: 0" (print_seg (Transform.Emitdfy.nearest_seg [] 10 10));
  ignore (Transform.Emitdfy.print_sourcemap !mapping)

let test_report_paths () =
  let source_map = ref [ ((1, 2), segment ~line:4 ~column:6 "x") ] in
  let output = "program.dfy(1,2): Error, a postcondition might not hold\n" in
  (match Run.Report.verification_errors ~sourcemap:source_map output with
   | Some errors -> check bool "verification error is reported" true (String.length errors > 0)
   | None -> fail "verification error should be recognized");
  check bool "non-error output has no locations" true
    (Option.is_none (Run.Report.verification_errors ~sourcemap:source_map "verified\n"));
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

let () =
  run "dafny-of-python"
    [ ("parser", [ test_case "typed assignment" `Quick test_parser_assignment
                  ; test_case "specifications and control flow" `Quick test_parser_specs_and_control_flow
                  ; test_case "fresh expression" `Quick test_parser_fresh
                  ; test_case "entry points and errors" `Quick test_parser_entry_points_and_errors
                  ; test_case "expression and type forms" `Quick test_parser_expression_and_type_forms
                  ; test_case "AST utilities" `Quick test_ast_utilities ])
    ; ("transforms", [ test_case "call state reset" `Quick test_transform_state_resets
                      ; test_case "emitter state reset" `Quick test_emitter_resets_state
                      ; test_case "Dafny 4 function syntax" `Quick test_dafny4_function_syntax
                      ; test_case "list conversion paths" `Quick test_convertlist_paths
                      ; test_case "call and for conversion" `Quick test_convertcall_and_convertfor_paths
                      ; test_case "generic conversion" `Quick test_generics_paths
                      ; test_case "call expression paths" `Quick test_convertcall_expression_paths
                      ; test_case "Dafny AST conversion" `Quick test_todafnyast_paths
                      ; test_case "emitter and source maps" `Quick test_emitter_paths_and_sourcemaps ])
    ; ("report", [ test_case "report parsing" `Quick test_report_paths ])
    ; ("pipeline", [ test_case "injected commands and cleanup" `Quick test_pipeline_injects_commands_and_cleans_files
                    ; test_case "failure and artifact paths" `Quick test_pipeline_failure_and_artifact_paths ])
    ]
