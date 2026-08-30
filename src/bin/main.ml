open Core

let printf = Stdlib.Printf.printf
let prerr = Stdlib.prerr_string

let resource_path name =
  let from_env =
    match Stdlib.Sys.getenv_opt "DAFNY_OF_PYTHON_RUNTIME_DIR" with
    | Some directory -> [ Filename.concat directory name ]
    | None -> []
  in
  let executable_dir = Filename.dirname Stdlib.Sys.argv.(0) in
  let candidates =
    from_env
    @ [ Filename.concat "src/libs/run" name
      ; Filename.concat executable_dir (Filename.concat "../libs/run" name)
      ; Filename.concat executable_dir (Filename.concat "../../libs/run" name)
      ; Filename.concat "/usr/local/share/dafny-of-python" name
      ; Filename.concat "/usr/share/dafny-of-python" name
      ]
  in
  match List.find candidates ~f:Stdlib.Sys.file_exists with
  | Some path -> path
  | None ->
    failwith
      ("Unable to locate runtime resource " ^ name
       ^ ". Pass an explicit --prelude/--list path or set "
       ^ "DAFNY_OF_PYTHON_RUNTIME_DIR.")

let main () =
  Pyparse.Parser.pp_exceptions ();
  let mypy = ref "mypy" in
  let dafny = ref "dafny" in
  (* Resolve defaults only after Arg.parse. This lets --help work from an
     installed directory without runtime resources and lets callers provide
     explicit paths when the default installation is absent. *)
  let prelude_override = ref None in
  let list_override = ref None in
  let temp_root = ref None in
  let keep_artifacts = ref false in
  let options =
    [ "--mypy", Arg.Set_string mypy, "Path or command name for mypy"
    ; "--dafny", Arg.Set_string dafny, "Path or command name for Dafny"
    ; "--prelude", Arg.String (fun path -> prelude_override := Some path),
      "Path to the Dafny prelude"
    ; "--list", Arg.String (fun path -> list_override := Some path),
      "Path to the Dafny list library"
    ; "--temp-root", Arg.String (fun path -> temp_root := Some path),
      "Directory in which temporary run directories are created"
    ; "--keep-artifacts", Arg.Set keep_artifacts,
      "Keep generated Python and Dafny files for debugging"
    ]
  in
  Arg.parse options (fun _ -> ()) "Translate typed Python from stdin to Dafny";
  let prelude = Option.value !prelude_override ~default:(resource_path "prelude.dfy") in
  let list_library = Option.value !list_override ~default:(resource_path "list.dfy") in
  let base_config = Run.Pipeline.default_config ~prelude ~list_library in
  let config =
    { base_config with
      mypy = !mypy
    ; dafny = !dafny
    ; temp_root = !temp_root
    ; keep_artifacts = !keep_artifacts
    }
  in
  let source = Stdio.In_channel.input_all Stdio.stdin in
  let result = Run.Pipeline.run ~config source in
  if result.typecheck.exit_code <> 0 then
    prerr
      ("\nTypechecking failed (exit code "
       ^ Int.to_string result.typecheck.exit_code
       ^ "):\n"
       ^ result.typecheck.stdout
       ^ result.typecheck.stderr
       ^ "\n");
  printf "\n%s\n" result.dafny_source;
  if String.length result.verification.stderr > 0 then
    prerr result.verification.stderr;
  Run.Report.report ~sourcemap:result.sourcemap result.verification.stdout;
  Run.Pipeline.exit_code result

let () =
  try Stdlib.exit (main ()) with
  | exn ->
    prerr (Stdlib.Printexc.to_string exn ^ "\n");
    Stdlib.exit 1
