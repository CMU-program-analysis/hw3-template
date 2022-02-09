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

let test_sigma_ne _ =
  let state1 = String.Map.of_alist_exn ["x", Top; "y", Top] in
  let state2 = String.Map.set state1 ~key:"x" ~data:Bot in 
  assert_equal (sigma_ne state1 state1) false;
  assert_equal (sigma_ne state1 state2) true

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
  let input = [ "x", Top; "y", Pos ] in
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
  let input = ["x", Top] in
  let operation = Lang.IfGoto ("x", Lang.EQ, 20) in
  let output = [ "x", Z ] in
  test_one_flow ~e:CondT input operation output

(* Tests an analysis *)
let run_analysis code expected_results =
  let lexbuf = Lexing.from_string code in
  let listing = Parser.listing Lexer.initial lexbuf in
  let cfg = Analysis.Cfg.of_listing listing in
  let results = kildall cfg |> string_of_results in
  (* DEBUG
  let _ = Printf.printf "Actual: %s\n" (results) in
  let _ = Printf.printf "Expected: %s\n" (expected_results) in 
  *)
  assert_equal results expected_results

let test_simple _ =
  let code =
    "1: x := 1\n2: y := 1\n3: x := x - y\n4: if x = 0 goto 7\n5: print y\n6: goto 8\n7: print x\n8: halt"
  in
  let expected_results =
    "Results before node n\n1: [ x = Top; y = Top; ]\n2: [ x = Pos; y = Top; ]\n3: [ x = Pos; y = Pos; ]\n4: [ x = Top; y = Pos; ]\n5: [ x = Top; y = Pos; ]\n6: [ x = Top; y = Pos; ]\n7: [ x = Z; y = Pos; ]\n8: [ x = Top; y = Pos; ]"
  in
  run_analysis code expected_results

let test_infloop _ =
  let code =
    "1: x := 0\n2: if x < 0 goto 6\n3: x := 1\n4: print x\n5: goto 2\n6: halt"
  in
  let expected_results =
    "Results before node n\n1: [ x = Top; ]\n2: [ x = Top; ]\n3: [ x = Top; ]\n4: [ x = Pos; ]\n5: [ x = Pos; ]\n6: [ x = Neg; ]"
  in
  run_analysis code expected_results

let tests = "tests" >::: [
  
    "test_alpha" >:: test_alpha;
    "test_join" >:: test_join;
    "test_sigma_ne" >:: test_sigma_ne;
    "test_flow" >:: test_flow;
    "test_simple" >:: test_simple;
    "test_infloop" >:: test_infloop;
  ]

let () =
  ignore (run_test_tt_main tests)
