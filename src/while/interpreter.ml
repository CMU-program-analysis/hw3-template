open Core
open Lang

let empty_state = String.Map.empty

let rec eval_aexp e = function
  | Num n -> n
  | Var x ->
     let n = String.Map.find_exn e x in
     n
  | Add (a1, a2) ->
     let n1 = eval_aexp e a1 in
     let n2 = eval_aexp e a2 in
     n1 + n2
  | Sub (a1, a2) ->
     let n1 = eval_aexp e a1 in
     let n2 = eval_aexp e a2 in
     n1 - n2
  | Mul (a1, a2) ->
     let n1 = eval_aexp e a1 in
     let n2 = eval_aexp e a2 in
     n1 * n2
  | Div (a1, a2) ->
     let n1 = eval_aexp e a1 in
     let n2 = eval_aexp e a2 in
     if n2 = 0 then failwith "division by zero" else n1 / n2

let rec eval_bexp e = function
  | True -> true
  | False -> false
  | Not p ->
     let b = eval_bexp e p in
     not b
  | And (p1, p2) ->
     let b1 = eval_bexp e p1 in
     let b2 = eval_bexp e p2 in
     b1 && b2
  | Or (p1, p2) ->
     let b1 = eval_bexp e p1 in
     let b2 = eval_bexp e p2 in
     b1 || b2
  | LT (a1, a2) ->
     let n1 = eval_aexp e a1 in
     let n2 = eval_aexp e a2 in
     n1 < n2
  | LEQ (a1, a2) ->
     let n1 = eval_aexp e a1 in
     let n2 = eval_aexp e a2 in
     n1 <= n2
  | EQ (a1, a2) ->
     let n1 = eval_aexp e a1 in
     let n2 = eval_aexp e a2 in
     n1 = n2
  | GT (a1, a2) ->
     let n1 = eval_aexp e a1 in
     let n2 = eval_aexp e a2 in
     n1 > n2
  | GEQ (a1, a2) ->
     let n1 = eval_aexp e a1 in
     let n2 = eval_aexp e a2 in
     n1 >= n2

let rec eval_stmt e = function
  | Skip -> e
  | Print a ->
     let n = eval_aexp e a in
     Format.printf "%d\n" n;
     e
  | Assign (x, a) ->
     let n = eval_aexp e a in
     let e' = String.Map.set e ~key:x ~data:n in
     e'
  | Seq (s1, s2) ->
     let e' = eval_stmt e s1 in
     let e'' = eval_stmt e' s2 in
     e''
  | If (p, s1, s2) ->
     let b = eval_bexp e p in
     let e' =
       if b then
         eval_stmt e s1
       else
         eval_stmt e s2
     in
     e'
  | While (p, s) ->
     let b = eval_bexp e p in
     let e'' =
       if b then
         let e' = eval_stmt e s in
         eval_stmt e' (While (p, s))
       else
         e
     in
     e''
  | Let (_, _, _) -> failwith "Let not implemented yet"
