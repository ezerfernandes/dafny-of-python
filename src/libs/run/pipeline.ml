open Base

type command =
  Pipeline_types.command

type command_result = Pipeline_types.command_result

type command_runner = Pipeline_types.command_runner

type config =
  { mypy : string
  ; dafny : string
  ; prelude : string
  ; list_library : string
  ; temp_root : string option
  ; keep_artifacts : bool
  ; runner : command_runner
  }

type result =
  { dafny_source : string
  ; sourcemap : Transform.Emitdfy.sourcemap
  ; typecheck : command_result
  ; verification : command_result
  ; working_directory : string option
  }

(* Verifier failure returns 1; a mypy failure returns 2 after translation;
   successful runs return 0. *)
let exit_code result =
  if result.verification.exit_code <> 0 then 1
  else if result.typecheck.exit_code <> 0 then 2
  else 0

let default_runner = Pipeline_runner.run

let close_noerr = Pipeline_runner.close_noerr
let read_available = Pipeline_runner.read_available
let status_code = Pipeline_runner.status_code

let default_config ~prelude ~list_library =
  { mypy = "mypy"
  ; dafny = "dafny"
  ; prelude
  ; list_library
  ; temp_root = None
  ; keep_artifacts = false
  ; runner = default_runner
  }

let write_file path contents = Stdio.Out_channel.write_all path ~data:contents

let make_temp_dir temp_root =
  let marker =
    match temp_root with
    | None -> Stdlib.Filename.temp_file "dafny-of-python-" ".tmp"
    | Some root -> Stdlib.Filename.temp_file ~temp_dir:root "dafny-of-python-" ".tmp"
  in
  Stdlib.Sys.remove marker;
  Unix.mkdir marker 0o700;
  marker

let remove_file path =
  try Stdlib.Sys.remove path with
  | Sys_error _ -> ()

let cleanup_directory config directory files =
  if not config.keep_artifacts then (
    List.iter files ~f:remove_file;
    try Unix.rmdir directory with
    | Unix.Unix_error _ -> ())

let run ~config source =
  let directory = make_temp_dir config.temp_root in
  let python_file = Stdlib.Filename.concat directory "program.py" in
  let dafny_file = Stdlib.Filename.concat directory "program.dfy" in
  let files = [ python_file; dafny_file ] in
  let cleanup () = cleanup_directory config directory files in
  try
    write_file python_file source;
    let typecheck = config.runner { program = config.mypy; args = [ python_file ] } in
    (* The historical CLI reports mypy failures but continues translating so
       that users can inspect the generated Dafny. Preserve that behavior and
       make the status available to callers instead of hiding it in stdout. *)
    let parsed = Pyparse.Parser.parse_string source in
    let dafny_ast = Transform.Todafnyast.prog_dfy parsed in
    let dafny_source, sourcemap = Transform.Emitdfy.print_prog_with_sourcemap dafny_ast in
    write_file dafny_file dafny_source;
    let verification =
      config.runner
        { program = config.dafny
        ; args =
            [ "verify"
            ; "--allow-warnings"
            ; dafny_file
            ; config.prelude
            ; config.list_library
            ]
        }
    in
    let result =
      { dafny_source
      ; sourcemap
      ; typecheck
      ; verification
      ; working_directory = if config.keep_artifacts then Some directory else None
      }
    in
    cleanup ();
    result
  with exn ->
    cleanup ();
    raise exn
