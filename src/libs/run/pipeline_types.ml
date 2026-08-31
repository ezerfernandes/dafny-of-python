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
