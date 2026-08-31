open Base

open Pipeline_types

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
let run ({ program; args } : command) =
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
      match !streams with
      | [] -> ()
      | _ ->
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
