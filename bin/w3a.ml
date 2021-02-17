open Core
open While3addr

let lexbuf = Lexing.from_channel In_channel.stdin
let prog = (1, Parser.listing Lexer.initial lexbuf)

let () =
  Interpreter.eval_program Interpreter.initial_env prog
