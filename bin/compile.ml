(* Compiles While code into While3addr *)

open Core
open While
open While3addr.Compile

let lexbuf = Lexing.from_channel In_channel.stdin
let stmt = Parser.program Lexer.initial lexbuf

let () =
  let (_pc, compiled_listing) = compile stmt in
  While3addr.Lang.string_of_listing compiled_listing
  |> Format.printf "%s\n"
