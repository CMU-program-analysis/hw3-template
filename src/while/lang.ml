open Core

type loc = string

type aexp =
  | Var of loc
  | Num of int
  | Add of aexp * aexp
  | Sub of aexp * aexp
  | Mul of aexp * aexp
  | Div of aexp * aexp

type bexp =
  | True
  | False
  | Not of bexp
  | And of bexp * bexp
  | Or of bexp * bexp
  | LT of aexp * aexp
  | LEQ of aexp * aexp
  | EQ of aexp * aexp
  | GT of aexp * aexp
  | GEQ of aexp * aexp

type stmt =
  | Skip
  | Assign of loc * aexp
  | Seq of stmt * stmt
  | If of bexp * stmt * stmt
  | While of bexp * stmt
  | Let of loc * aexp * stmt
  | Print of aexp

let rec aexp_to_str = function
  | Var v -> v
  | Num n -> string_of_int n
  | Add (a1, a2) -> Format.sprintf "(%s + %s)" (aexp_to_str a1) (aexp_to_str a2)
  | Sub (a1, a2) -> Format.sprintf "(%s - %s)" (aexp_to_str a1) (aexp_to_str a2)
  | Mul (a1, a2) -> Format.sprintf "(%s * %s)" (aexp_to_str a1) (aexp_to_str a2)
  | Div (a1, a2) -> Format.sprintf "(%s / %s)" (aexp_to_str a1) (aexp_to_str a2)

and bexp_to_str = function
  | True -> "true"
  | False -> "false"
  | Not b -> Format.sprintf "!%s" (bexp_to_str b)
  | And (b1, b2) -> Format.sprintf "(%s && %s)" (bexp_to_str b1) (bexp_to_str b2)
  | Or (b1, b2) -> Format.sprintf "(%s || %s)" (bexp_to_str b1) (bexp_to_str b2)
  | LT (a1, a2) -> Format.sprintf "(%s < %s)" (aexp_to_str a1) (aexp_to_str a2)
  | LEQ (a1, a2) -> Format.sprintf "(%s <= %s)" (aexp_to_str a1) (aexp_to_str a2)
  | EQ (a1, a2) -> Format.sprintf "(%s = %s)" (aexp_to_str a1) (aexp_to_str a2)
  | GT (a1, a2) -> Format.sprintf "(%s > %s)" (aexp_to_str a1) (aexp_to_str a2)
  | GEQ (a1, a2) -> Format.sprintf "(%s >= %s)" (aexp_to_str a1) (aexp_to_str a2)

and stmt_to_str = function
  | Skip -> "skip"
  | Assign (l, a) -> Format.sprintf "%s := %s" l (aexp_to_str a)
  | Seq (s1, s2) -> Format.sprintf "%s; %s" (stmt_to_str s1) (stmt_to_str s2)
  | If (pred, sthen, selse) ->
     let pred = bexp_to_str pred in
     let sthen = stmt_to_str sthen in
     let selse = stmt_to_str selse in
     Format.sprintf "if %s then %s else %s" pred sthen selse
  | While (pred, body) ->
     let pred = bexp_to_str pred in
     let body = stmt_to_str body in
     Format.sprintf "while %s do %s" pred body
  | Let (l, a, body) ->
     Format.sprintf "let %s = %s in %s" l (aexp_to_str a) (stmt_to_str body)
  | Print a -> Format.sprintf "print %s" (aexp_to_str a)
