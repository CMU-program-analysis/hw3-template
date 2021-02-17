{
open Core
open Parser
}

let blank = [' ' '\012' '\r' '\t' '\n']

rule initial = parse
  blank { initial lexbuf }
| '+'           { PLUS }
| '-'           { MINUS }
| '*'           { TIMES }
| '/'           { DIV }
| ':'           { COLON }
| "="           { EQ_TOK }
| "<"           { LT_TOK }
| ":="          { SET }
| "if"          { IF }
| "goto"        { GOTO }
| "print"       { PRINT }
| "halt"        { HALT }

| ['1'-'9']['0'-'9']* {
  let str = Lexing.lexeme lexbuf in
  POSITIVE((int_of_string str)) }

| '0' { ZERO }

| ("0x")?'-'?['0'-'9']+ {
  let str = Lexing.lexeme lexbuf in
  INT((int_of_string str)) }

| ['A'-'Z''a'-'z''_']['0'-'9''A'-'Z''a'-'z''_']* {
  let str = Lexing.lexeme lexbuf in
  IDENTIFIER(str)
  }
| '.'
| eof     { EOF }
| _       {
  Printf.printf "invalid character '%s'\n" (Lexing.lexeme lexbuf) ;
  (* this is not the kind of error handling you want in real life *)
  exit 1 }

and endline = parse
        '\n'      { initial lexbuf}
| _               { endline lexbuf}
|       eof       { EOF }
