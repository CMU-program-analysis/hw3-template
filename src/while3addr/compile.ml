open Core
open Lang
module While = While.Lang

let getop = function
  | While.Add _ -> Add
  | While.Sub _ -> Sub
  | While.Mul _ -> Mul
  | While.Div _ -> Div
  | _ -> failwith "getopt on non-arithmetic operation"

let newIfGoto v op target = IfGoto (v, op, target)

let invert_not = function
  | While.True -> While.False
  | While.False -> While.True
  | While.Not b -> b
  | While.And (b1, b2) -> While.Or (While.Not(b1), While.Not(b2))
  | While.Or (b1, b2) -> While.And (While.Not(b1), While.Not(b2))
  | While.LT (a1, a2) -> While.GEQ (a1, a2)
  | While.LEQ (a1, a2) -> While.GT (a1, a2)
  | While.EQ (a1, a2) -> While.Or (While.LT(a1, a2), While.GT(a1, a2))
  | While.GT (a1, a2) -> While.LEQ (a1, a2)
  | While.GEQ (a1, a2) -> While.LT (a1, a2)

let newvars = ref 0

let fresh () =
  incr newvars;
  Printf.sprintf "a%d" !newvars

let append_to_program (pc, p) (instr) : program =
  pc + 1, Int.Map.set p ~key:pc ~data:instr

let insert_in_program (pc,p) i (instr) = pc,Int.Map.set p ~key:i ~data:instr

let compile stmt =
  let rec transform_aexp prog = function
    | While.Var z -> prog, z
    | While.Num n ->
       let v = fresh () in
       append_to_program prog (ConstAssign (v, n)), v
    | While.Add (a1, a2)
      | While.Sub (a1, a2)
      | While.Mul (a1, a2)
      | While.Div (a1, a2) as aexp ->
       let myop = getop aexp in
       let v0 = fresh () in
       let prog', v1 = transform_aexp prog a1 in
       let prog'', v2 = transform_aexp prog' a2 in
       append_to_program prog'' (OpAssign(v0, v1, v2, myop)), v0
  and transform_cond prog = function
    (* Check that v0 equals 0 *)
    | While.True ->
       let v0 = fresh () in
       v0, EQ, append_to_program prog (ConstAssign(v0, 0))
    | While.False ->
       let v0 = fresh () in
       v0, EQ, append_to_program prog (ConstAssign(v0, 1))
    | While.LT (Var(z), Num(0)) -> (* a lil special casing... *)
       z, LT, prog
    | While.LT (a1, Num(0)) ->
       let prog, v1 = transform_aexp prog a1 in
       v1,LT,prog
    | While.LT (a1,a2) ->
       let v0 = fresh () in
       let prog', v1 = transform_aexp prog a1 in
       let prog'', v2 = transform_aexp prog' a2 in
       v0, LT, append_to_program prog'' (OpAssign (v0, v1, v2, Sub))
    | While.GT (a1, a2) ->
       let v0 = fresh () in
       let prog', v1 = transform_aexp prog a1 in
       let prog'', v2 = transform_aexp prog' a2 in
       v0, LT, append_to_program prog'' (OpAssign (v0, v2, v1, Sub))
    | While.EQ(Var(z),Num(0)) -> z,EQ, prog
    | While.EQ(a1,Num(0)) ->
       let prog,v1 = transform_aexp prog a1 in
       v1,EQ,prog
    | While.EQ (a1, a2) ->
       let v0 = fresh () in
       let prog', v1 = transform_aexp prog a1 in
       let prog'', v2 = transform_aexp prog' a2 in
       v0, EQ, append_to_program prog'' (OpAssign (v0, v1, v2, Sub))
    | While.Not b -> transform_cond prog (invert_not b)
    | While.LEQ (a1, a2) ->
       transform_cond prog (Or ((LT (a1, a2)), (EQ (a1, a2))))
    | While.GEQ (a1, a2) -> transform_cond prog (LT (a2, a1))
    | While.And (b1, b2) -> (* I know this is hideous, hard to keep all the pieces in my head *)
       (* basically, we do:
          if (b1 and b2) -->
          0. goto 5
          1. a0 = 0
          2. goto 4
          3. a0 = 1
          4. goto 9
          5. if (b1) goto 7
          6. goto 3
          7. if (b2) goto 1
          8. goto 3
          9.
          ...and the equivalent for "or"
        *)
       let ares = fresh() in
       let goto_start_of_if,prog = prog in
       let jump_to_if = (fun prog pc -> insert_in_program prog goto_start_of_if (Goto(pc))) in
       let thenstart = goto_start_of_if + 1 in
       let jump_to_end_of_else,prog = append_to_program (thenstart, prog) (ConstAssign(ares,0)) in
       let (elsepc,prog) = append_to_program (jump_to_end_of_else,prog) (Goto(jump_to_end_of_else+2)) in
       let jump_to_end_of_if,prog = append_to_program (elsepc,prog) (ConstAssign(ares,1)) in
       let jump_over_if = (fun prog pc -> insert_in_program prog jump_to_end_of_if (Goto(pc))) in
       let b1v,op1,(start_of_if,prog) = transform_cond (jump_to_end_of_if+1,prog) b1 in
       let (end_of_b1_if,prog) = append_to_program (start_of_if,prog) (IfGoto(b1v,op1,start_of_if + 2)) in
       let (nextcond,prog) = append_to_program (end_of_b1_if,prog) (Goto(elsepc)) in
       let b2v,op2,(b2pc,prog) = transform_cond (nextcond,prog) b2 in
       let (ifpc,prog) = append_to_program (b2pc,prog) (IfGoto(b2v,op2,thenstart)) in
       let (afterif,prog) = append_to_program (ifpc,prog) (Goto(elsepc)) in
       let prog = jump_over_if (afterif,prog) afterif in
       let prog = jump_to_if prog (jump_to_end_of_if + 1) in
       ares,EQ,prog
    | While.Or (b1, b2) ->
       let ares = fresh() in
       let goto_start_of_if,prog = prog in
       let jump_to_if = (fun prog pc -> insert_in_program prog goto_start_of_if (Goto(pc))) in
       let thenstart = goto_start_of_if + 1 in
       let jump_to_end_of_else,prog = append_to_program (thenstart, prog) (ConstAssign(ares,0)) in
       let (elsepc,prog) = append_to_program (jump_to_end_of_else,prog) (Goto(jump_to_end_of_else+2)) in
       let jump_to_end_of_if,prog = append_to_program (elsepc,prog) (ConstAssign(ares,1)) in
       let jump_over_if = (fun prog pc -> insert_in_program prog jump_to_end_of_if (Goto(pc))) in

       let b1v,op1,(start_of_if,prog) = transform_cond (jump_to_end_of_if+1,prog) b1 in
       let prog = append_to_program (start_of_if,prog) (IfGoto(b1v,op1,thenstart)) in
       let b2v,op2,(b2pc,prog) = transform_cond prog b2 in
       let (ifpc,prog) = append_to_program (b2pc,prog) (IfGoto(b2v,op2,thenstart)) in
       let (afterif,prog) = append_to_program (ifpc,prog) (Goto(elsepc)) in
       let prog = jump_over_if (afterif,prog) afterif in
       let prog = jump_to_if prog (jump_to_end_of_if + 1) in (* start_of_if is wrong *)
       ares,EQ,prog
  and transform_stmt prog = function
    | While.Skip -> prog
    | While.Print aexp ->
       let prog',v0 = transform_aexp prog aexp in
       append_to_program prog' (Print v0)
    | While.Assign (x, Var y) -> append_to_program prog (VarAssign (x, y))
    | While.Assign (x, Num n) -> append_to_program prog (ConstAssign (x, n))
    | While.Assign(x, aexp) ->
       let prog', v2 = transform_aexp prog aexp in
       append_to_program prog' (VarAssign (x, v2))
    | While.Seq (s1, s2) -> transform_stmt (transform_stmt prog s1) s2
    | While.If (b, s1, s2) ->
       (* if B then s1 else s2 -->
          goto [startofif]
          then
          goto [end of ifcmp]
          else [start of else ]
          got [end of ifmp]
          startofifcmp: a0 = transform(b)
          if (a0) goto startofthen
          goto startofelse
          ...end of *)
       let goto_ifstart_pc,prog = prog in
       let then_start = goto_ifstart_pc + 1 in
       let (jump_past_else_if_goto,prog) = transform_stmt (then_start,prog) s1 in
       let else_start = jump_past_else_if_goto + 1 in
       let (jump_past_if,prog) = transform_stmt (else_start,prog) s2 in
       let start_of_if = jump_past_if + 1 in
       let (_,prog) = insert_in_program (jump_past_if,prog) goto_ifstart_pc (Goto(start_of_if)) in
       let v,op,(pc,prog)= transform_cond (start_of_if,prog) b in
       let prog = append_to_program (pc,prog) (IfGoto(v,op,then_start)) in
       let pc,prog = append_to_program prog (Goto(else_start)) in
       let prog = insert_in_program (pc,prog) jump_past_if (Goto(pc)) in
       insert_in_program prog jump_past_else_if_goto (Goto(jump_past_if))
    | While.While (b, s) ->
       (* while b do s1 -->
          1. if not b goto 4
          2. s1
          3. goto 1
          4. *)
       let startpc, _ = prog in
       let v,op,(ifpc,prog) = transform_cond prog (Not b) in
       let jump_over_while = (fun prog pc -> insert_in_program prog ifpc (IfGoto(v,op,pc))) in
       (* if pc is where the first if foo goto bar goes, and the target of the
          goto at the end of the while loop body *)
       let start_of_while_body = ifpc + 1 in
       let prog = transform_stmt (start_of_while_body, prog) s in
       let after_body_pc, prog = append_to_program prog (Goto(startpc)) in
       jump_over_while (after_body_pc,prog) after_body_pc
    | While.Let _ -> failwith "Let translation to while3addr is not implemented and not \
                              part of this assignment; try While code without Let \
                              instead"

  in
  let prog = transform_stmt (1, Int.Map.empty) stmt in
  append_to_program prog (Halt)
