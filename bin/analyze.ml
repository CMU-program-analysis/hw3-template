open Analysis
open Core
open While3addr

let lexbuf = Lexing.from_channel In_channel.stdin
let listing = Parser.listing Lexer.initial lexbuf

let () =
  let cfg = Cfg.of_listing listing in
  Analysis.Df.kildall cfg
  |> Analysis.Df.string_of_results
  |> Format.printf "%s\n"
