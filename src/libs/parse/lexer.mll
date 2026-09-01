{
  [@@@coverage exclude_file]

  open Menhir_parser

  exception LexError of string
  let printf = Stdlib.Printf.printf
  let[@inline] failwith msg = raise (LexError msg)
  let[@inline] illegal c =
    failwith (Printf.sprintf "[lexer] unexpected character: '%c'" c)

  let strip_quotes str =
    match String.length str with
    | 0 | 1 | 2 -> ""
    | len -> String.sub str 1 (len - 2)

  let emit_segment lb v = 
    let s = Lexing.lexeme_start_p lb in
    (s, v)

  let emit_lexeme lb = emit_segment lb (Some (Lexing.lexeme lb))

  let next_line (lb: Lexing.lexbuf) cols =
    let lcp = lb.lex_curr_p in
    lb.lex_curr_p <- { lcp with
      pos_lnum = lcp.pos_lnum + 1;
      pos_cnum = lcp.pos_cnum + cols;
      pos_bol = lcp.pos_cnum - cols;
    }   
}

let indent = '\n' [' ' '\t']*
let whitespace = [' ' '\t']+

(* simple types *)
let int_typ = "int"
let float_typ = "float"
let bool_typ = "bool"
let str_typ = "str"
(* let none_typ = "None" *)
let obj_typ = "object"

(* complex types *)
let list_typ = "list"
let dict_typ = "dict"
let set_typ = "set"
let tuple_typ = "tuple"
let callable_typ = "Callable"
let type_typ = "Type"
let union_typ = "Union"

let typ = int_typ | float_typ | bool_typ | str_typ | obj_typ | list_typ | dict_typ | set_typ
let typ_f = typ '('

let identifier = ['a'-'z' 'A'-'Z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*
let digit = ['0'-'9']
let integer = digit digit*
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = '-'? (frac exp | digit+ exp | digit+ frac exp | digit* frac)
let strliteral = ('"'[^'"''\\']*('\\'_[^'"''\\']*)*'"')
let comment = '#'
let boolean = "True" | "False"

let pre = '#' [' ' '\t']* "pre"
let post = '#' [' ' '\t']* "post"
let invariant = '#' [' ' '\t']* "invariant"
let decreases = '#' [' ' '\t']* "decreases"
let reads = '#' [' ' '\t']* "reads"
let modifies = '#' [' ' '\t']* "modifies"

rule next_token = parse
| eof { EOF }
| typ_f as tf 
  { let s = (
      String.sub tf 0 ((String.length tf) - 1)
    ) ^ "F" in TYPF (emit_segment lexbuf (Some s)) 
  }
| int_typ { INT_TYP (emit_lexeme lexbuf) }
| float_typ { FLOAT_TYP (emit_lexeme lexbuf) }
| bool_typ { BOOL_TYP (emit_lexeme lexbuf) }
| str_typ { STRING_TYP (emit_lexeme lexbuf) }
| obj_typ { OBJ_TYP (emit_lexeme lexbuf) }
| list_typ { LIST_TYP (emit_segment lexbuf (Some "List")) }
| dict_typ { DICT_TYP (emit_lexeme lexbuf) }
| set_typ { SET_TYP (emit_lexeme lexbuf) }
| tuple_typ { TUPLE_TYP (emit_lexeme lexbuf) }
| callable_typ { CALLABLE_TYP (emit_lexeme lexbuf) }
| type_typ { TYPE_TYP (emit_lexeme lexbuf) }
| union_typ { UNION_TYP (emit_lexeme lexbuf) }
| indent as s { (next_line lexbuf (String.length s - 1); SPACE (String.length s - 1)) }
| "import" { comment lexbuf }
| "from" { comment lexbuf }
| pre { PRE }
| post { POST }
| invariant { INVARIANT }
| decreases { DECREASES }
| reads { READS }
| modifies { MODIFIES }
| "forall" { FORALL }
| "exists" { EXISTS }
| "<==>" { BIIMPL (emit_segment lexbuf (Some "<==>" )) }
| "==>" { IMPLIES (emit_segment lexbuf (Some "==>" )) }
| "<==" { EXPLIES (emit_segment lexbuf (Some "<==" )) }
| "::" { DOUBLECOLON }
| '(' { LPAREN }
| ')' { RPAREN }
| '{' { LBRACE }
| '}' { RBRACE }
| '['  { LBRACK }
| ']' { RBRACK }
| '.' { DOT }
| ':' { COLON }
| ';' { SEMICOLON }
| ',' { COMMA (emit_lexeme lexbuf) }
| "old" { OLD (emit_lexeme lexbuf) }
| "fresh" { FRESH (emit_lexeme lexbuf) }
| "len" { LEN (emit_lexeme lexbuf) }
| "max" { MAX (emit_lexeme lexbuf) }
| "filter" { IDENTIFIER (emit_segment lexbuf (Some "filterF")) }
| "map" { IDENTIFIER (emit_segment lexbuf (Some "mapF")) }
| "->" { ARROW }
| "def" { DEF (emit_lexeme lexbuf) }
| "lambda" { LAMBDA (emit_lexeme lexbuf) }
| "if" { IF (emit_lexeme lexbuf) }
| "elif" { ELIF (emit_lexeme lexbuf) }
| "else" { ELSE (emit_lexeme lexbuf) }
| "for" { FOR (emit_lexeme lexbuf) }
| "while" { WHILE (emit_lexeme lexbuf) }
| "break" { BREAK (emit_lexeme lexbuf) }
| "pass" { PASS (emit_lexeme lexbuf) }
| "return" { RETURN (emit_lexeme lexbuf) }
| "assert" { ASSERT (emit_lexeme lexbuf) }
| "not in" { NOT_IN (emit_lexeme lexbuf) }
| "in" { IN (emit_lexeme lexbuf) }
| "==" { EQEQ (emit_lexeme lexbuf) }
| '=' { EQ (emit_lexeme lexbuf) }
| "!=" { NEQ (emit_lexeme lexbuf) }
| '+' { PLUS (emit_lexeme lexbuf) }
| "+=" { PLUSEQ (emit_lexeme lexbuf) }
| '-' { MINUS (emit_lexeme lexbuf) }
| "-=" { MINUSEQ (emit_lexeme lexbuf) }
| '*' { TIMES (emit_lexeme lexbuf) }
| "*=" { TIMESEQ (emit_lexeme lexbuf) }
| "/" { DIVIDE (emit_lexeme lexbuf) }
| "/=" { DIVIDEEQ (emit_lexeme lexbuf) }
| "%" { MOD (emit_lexeme lexbuf) }
| "<=" { LTE (emit_lexeme lexbuf) }
| '<' { LT (emit_lexeme lexbuf) }
| ">=" { GTE (emit_lexeme lexbuf) }
| '>' { GT (emit_lexeme lexbuf) }
| "and" { AND (emit_lexeme lexbuf) }
| "or" { OR (emit_lexeme lexbuf) }
| "not" { NOT (emit_lexeme lexbuf) }
| "True" { TRUE }
| "False" { FALSE }
| "None" { NONE (emit_lexeme lexbuf) }
| float as f { FLOAT f }
| integer as i { INT i }
| identifier as i { IDENTIFIER (emit_segment lexbuf (Some i)) }
| strliteral as s { STRING (strip_quotes s) }
| whitespace { next_token lexbuf }
| comment { comment lexbuf }
| _ as c { illegal c }

and comment = parse
| indent as s { (next_line lexbuf (String.length s - 1); next_token lexbuf) } 
| _ { comment lexbuf }
