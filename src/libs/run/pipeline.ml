open Base

type command =
  { program : string
  ; args : string list
  }

type command_result =
  { exit_code : int
  ; stdout : string
  ; stderr : string
  }

type command_runner = command -> command_result

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

(* Exit-code policy used by the CLI: verifier/translation failure is fatal
   (1); a mypy failure is reported after translation and returns 2 when Dafny
   succeeds; a fully successful run returns 0. *)
let exit_code result =
  if result.verification.exit_code <> 0 then 1
  else if result.typecheck.exit_code <> 0 then 2
  else 0

let close_noerr fd =
  try Unix.close fd with
  | Unix.Unix_error _ -> ()

let rec read_available read fd bytes =
  try read fd bytes 0 (Bytes.length bytes) with
  | Unix.Unix_error (Unix.EINTR, _, _) -> read_available read fd bytes

let status_code = function
  | Unix.WEXITED code -> code
  | Unix.WSIGNALED signal -> 128 + signal
  | Unix.WSTOPPED signal -> 128 + signal

(* Read both pipes concurrently. Reading stdout to completion before stderr can
   deadlock when a verifier emits enough diagnostics to fill stderr. *)
let default_runner ({ program; args } : command) =
  let stdout_read, stdout_write = Unix.pipe () in
  let stderr_read, stderr_write = Unix.pipe () in
  let argv = Array.of_list (program :: args) in
  try
    let pid = Unix.create_process program argv Unix.stdin stdout_write stderr_write in
    close_noerr stdout_write;
    close_noerr stderr_write;
    let stdout_buffer = Stdlib.Buffer.create 1024 in
    let stderr_buffer = Stdlib.Buffer.create 1024 in
    let streams = ref [ (stdout_read, stdout_buffer); (stderr_read, stderr_buffer) ] in
    let rec drain () =
      if List.is_empty !streams then ()
      else
        let fds = List.map !streams ~f:fst in
        let ready, _, _ = Unix.select fds [] [] (-1.0) in
        List.iter ready ~f:(fun fd ->
          let _, buffer =
            List.find_exn !streams ~f:(fun (candidate, _) -> Stdlib.compare candidate fd = 0)
          in
          let bytes = Bytes.create 4096 in
          match read_available Unix.read fd bytes with
          | 0 ->
            close_noerr fd;
            streams := List.filter !streams ~f:(fun (candidate, _) -> Stdlib.compare candidate fd <> 0)
          | count -> Stdlib.Buffer.add_subbytes buffer bytes 0 count);
        drain ()
    in
    drain ();
    let _, status = Unix.waitpid [] pid in
    { exit_code = status_code status
    ; stdout = Stdlib.Buffer.contents stdout_buffer
    ; stderr = Stdlib.Buffer.contents stderr_buffer
    }
  with exn ->
    close_noerr stdout_read;
    close_noerr stdout_write;
    close_noerr stderr_read;
    close_noerr stderr_write;
    { exit_code = 127
    ; stdout = ""
    ; stderr = Stdlib.Printexc.to_string exn
    }

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
