open Core
open Lang

let initial_env = String.Map.empty

let eval_insn env pc insn =
  let update env id value = String.Map.set env ~key:id ~data:value in
  let lookup = String.Map.find_exn in
  match insn with
  | ConstAssign (v, n) ->
     let new_env = update env v n in
     `Continue (pc + 1, new_env)
  | VarAssign (v1, v2) ->
     let n = lookup env v2 in
     let new_env = update env v1 n in
     `Continue (pc + 1, new_env)
  | OpAssign (v, v1, v2, op) ->
     let n1 = lookup env v1 in
     let n2 = lookup env v2 in
     let int_op =
       match op with
       | Add -> (+)
       | Sub -> (-)
       | Mul -> ( * )
       | Div -> (/)
     in
     let result = int_op n1 n2 in
     let new_env = update env v result in
     `Continue (pc + 1, new_env)
  | Goto location -> `Continue (location, env)
  | IfGoto (v, opr, lineno) ->
     let n = lookup env v in
     let comparison =
       match opr with
       | LT -> (<)
       | EQ -> (=)
     in
     if (comparison n 0) then
       `Continue (lineno, env)
     else
       `Continue (pc + 1, env)
  | Print v ->
     let n = lookup env v in
     Format.printf "%d\n" n;
     `Continue (pc + 1, env)
  | Halt -> `Halt

let rec eval_program env (pc, listing) =
  let fetch location =
    match Int.Map.find listing location with
    | None -> Format.sprintf "No instruction at %d" location |> failwith
    | Some instruction -> instruction
  in
  match eval_insn env pc (fetch pc) with
  | `Continue (next_pc, new_env) -> eval_program new_env (next_pc, listing)
  | `Halt -> ()
