open Core
open OUnit
open Analysis.Df
open While3addr

let test_alpha _ =
  assert_equal (alpha 0) Z

let test_join _ =
  assert_equal (join_values Neg Top) Top;
  assert_equal (join_values Neg Neg) Neg;
  assert_equal (join_values Pos Pos) Pos

let test_le _ =
  assert_equal (le_values Top Top) true;
  assert_equal (le_values Top Bot) false

let test_flow _ =
  (* Tests a flow function by comparing actual and expected changes in sigma *)
  let test_one_flow ?e:(e_type=Analysis.Cfg.NoEdge) input code expected =
    let sigma_in = String.Map.of_alist_exn input in
    let sigma_out = flow sigma_in code e_type in
    let expected_out = String.Map.of_alist_exn expected in
    String.Map.iter2 expected_out sigma_out ~f:(fun ~key ~data ->
        match data with
        | `Left _ | `Right _ -> assert_failure "sigma"
        | `Both (l, r) -> assert_equal l r
      )
  in
  (* Test a constant assignment to zero. We expect that if x starts as Top, it
     should end up as Z *)
  let input = [ "x", Top ] in
  let operation = Lang.ConstAssign ("x", 0) in
  let output = [ "x", Z ] in
  test_one_flow input operation output;
  (* Test a variable assignment. We expect that if y starts as Pos, and x is
     assigned y, then x and y should both end up as Pos *)
  let input = [ "y", Pos ] in
  let operation = Lang.VarAssign ("x", "y") in
  let output = [ "x", Pos; "y", Pos ] in
  test_one_flow input operation output;
  (* Test an operator assignment. We expect that a positive plus a positive is a
     positive *)
  let input = [ "y", Pos; "z", Pos ] in
  let operation = Lang.OpAssign ("x", "y", "z", Lang.Add) in
  let output = [ "x", Pos; "y", Pos; "z", Pos ] in
  test_one_flow input operation output;
  (* Test the true branch of an if. If we're on the true branch of `if x = 0
     goto 20`, x should be Z *)
  let input = [] in
  let operation = Lang.IfGoto ("x", Lang.EQ, 20) in
  let output = [ "x", Z ] in
  test_one_flow ~e:CondT input operation output

(* Tests an analysis *)
let run_analysis code expected_results =
  let lexbuf = Lexing.from_string code in
  let listing = Parser.listing Lexer.initial lexbuf in
  let cfg = Analysis.Cfg.of_listing listing in
  let results = kildall cfg |> string_of_results in
  assert_equal results expected_results

let test_simple _ =
  let code =
    "1: x := 0\n2: y := 0\n3: if x = 0 goto 6\n4: print y\n5: goto 7\n6: print x\n7: halt"
  in
  let expected_results =
    "Results before node n\n1: [ ]\n2: [ x = Z; ]\n3: [ x = Z; y = Z; ]\n4: [ x = Top; y = Z; ]\n5: [ x = Top; y = Z; ]\n6: [ x = Z; y = Z; ]\n7: [ x = Top; y = Z; ]"
  in
  run_analysis code expected_results

let tests = "tests" >::: [
    "test_alpha" >:: test_alpha;
    "test_join" >:: test_join;
    "test_le" >:: test_le;
    "test_flow" >:: test_flow;
    "test_simple" >:: test_simple
  ]

let () =
  ignore (run_test_tt_main tests)