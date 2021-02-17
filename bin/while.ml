(* Interprets a while program input on stdin *)

open Core
open While

let lexbuf = Lexing.from_channel In_channel.stdin
let stmt = Parser.program Lexer.initial lexbuf

let () =
  ignore (Interpreter.eval_stmt Interpreter.empty_state stmt);
