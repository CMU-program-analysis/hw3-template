open Core

open While3addr.Lang

type domain =
  | Top
  | Neg
  | Z
  | Pos
  | Bot

let string_of_dom = function
  | Top -> "Top"
  | Neg -> "Neg"
  | Z -> "Z"
  | Pos -> "Pos"
  | Bot -> "Bot"

(* the state sigma maps variable names to abstract values *)
type sigma = domain String.Map.t

(* Returns a printable string for a state  *)
let string_of_sigma sigma =
  let show_abstract_val ~key:variable ~data:abstract_value values =
    Format.sprintf "%s%s = %s; " values variable (string_of_dom abstract_value)
  in
  let values = String.Map.fold sigma ~init:"" ~f:show_abstract_val in
  Format.sprintf "[ %s]" values

(* The results of a dataflow analysis is a mapping between program points and
   dataflow state at those points. More specifically, here, we are using
   Kildall's algorithm to compute the input dataflow state to every instruction
   in a While3Addr program. We store this in a datastructure that maps integers
   (node numbers) to sigma (states) *)
type df_results = sigma Int.Map.t

(* Returns a printable string for dataflow results before each program point *)
let string_of_results results =
  let show_result ~key:location ~data:sigma results =
    Format.sprintf "%s\n%d: %s" results location (string_of_sigma sigma)
  in
  Int.Map.fold results ~init:"Results before node n" ~f:show_result

(* Same as above, but also interleaves a listing of the program *)
let string_of_results_listing listing results =
  let show_instr ~key:loc ~data:instr collected =
    let result =
      match Int.Map.find results loc with
      | None -> "[ ]"
      | Some sigma -> string_of_sigma sigma
    in
    Format.sprintf "%s\n%s\n%s" collected result (string_of_instr loc instr)
  in
  Int.Map.fold listing ~init:"Results:" ~f:show_instr

(* TODO
   alpha abstracts concrete values in your language to abstract values. Concrete
   values in while3Addr are integers. Your implementation should work on all of
   the abstract values in the domain defined above. *)
let alpha (n : int) : domain = failwith "Implement me!"
 
(* TODO
   the join function merges two states into a new state. It works by lifting a
   value-specific join from individual variables to maps. We have implemented
   the lifted version for you, below, but you still need to implement this
   function that joins two abstract values. *)
let join_values (v1 : domain) (v2 : domain) = failwith "Implement me!"

(* Joins two states into a new input state. In this implementation, we do this
   by taking advantage of Map.merge; the interesting/analysis-specific part is
   in join_values, above, so we've done this part for you *)
let join (state1 : sigma) (state2 : sigma) : sigma =
  String.Map.merge state1 state2
    ~f:(fun ~key:_ -> function
      | `Left v | `Right v ->  failwith "States contain different number of variables!"
      | `Both (v1, v2) -> Some (join_values v1 v2))
      
(* TODO
   For Kildall's algorithm ur termination condition relies on the ability to tell whether one
   abstract state is "not equal to" another. Since our abstract state in this analysis is a map
   over variables, you will need to lift the inequality check from individual variables to maps *)
let sigma_ne (state1 : sigma) (state2 : sigma) : bool = failwith "Implement me!"
 
(* OCaml lets you define infix operators by putting them inside parens. Only
   certain characters are allowed to be used as operators:
   http://caml.inria.fr/pub/docs/manual-ocaml/lex.html#infix-symbol

   We defined this operator for you so you can use `s1 != s2` in this module to
   compare two states, but you can still use `sigma_ne s1 s2` if you'd like. *)
let (!=) = sigma_ne


(* TODO
   Given an input state and an instruction, the flow function returns a new
   state. To get you started, we wrote a couple of the simpler cases. We also
   added a few more arguments to this flow function beyond the code and the
   input state: the id of the current node, and the kind of edge this new state
   will be flowing down. This last piece of information is probably only
   interesting to you when processing if statements; all other nodes only have
   direct edges to their successors! *)
let flow (state : sigma) (code : instr) (e_type : Cfg.edge): sigma =
  match code with
  (* These instructions don't modify the state *)
  | Goto _ | Print _ | Halt -> state
  (* A constant assignment updates the state with a mapping from the variable to
     the abstract value of n (i.e., alpha n). Since the Map data structure from
     the OCaml Core library is functional, we can just return the result of
     `set`, which is an updated Map containing our new binding *)
  | ConstAssign (v1, n) -> String.Map.set state ~key:v1 ~data:(alpha n)
  (* A variable assigment updates the state with a mapping from the target
     variable to the abstract value of the source variable. We use `find_exn` to
     get the source value, which raises an exception if it doesn't exist (if it
     doesn't exist the program is malformed). *)
  | VarAssign (v1, v2) -> String.Map.set state ~key:v1 ~data:(String.Map.find_exn state v2)
  (* TODO
     `v0 := v1 op v2` where `op` is one of `Add | Sub | Mul | Div`
  *)
  | OpAssign (v0, v1, v2, op) -> failwith "Implement me!"
  (* TODO
     `if v1 opr 0 goto n` where `opr` is one of `LT | EQ`
     Check handling of CondF: what if more specific state is valid?
  *)
  | IfGoto (v1, opr, n) -> failwith "Implement me!"
      
(* This initializes a state for the cfg by mapping all variables to the passed in abstract value *)      
let initializeSigma (cfg: Cfg.t) (value: domain) : sigma = 
  let nodes = Int.Map.keys cfg.nodes in 
  let add_var (s) (n) =
    match (Int.Map.find_exn cfg.nodes n) with
    | ConstAssign (v1, _) -> String.Map.set s ~key:v1 ~data:value 
    | VarAssign (v1, _) -> String.Map.set s ~key:v1 ~data:value
    | OpAssign (v0, _, _, _) -> String.Map.set s ~key:v0 ~data:value
    | _ -> s
  in
  List.fold nodes ~init:(String.Map.empty) ~f:(add_var)
 
(* TODO
   Complete Kildall's algorithm
 *)
let kildall (cfg : Cfg.t) : df_results =
  let rec work (inputs : df_results) = function
    | [] -> inputs (* while worklist is not empty *)
    | n :: ns -> (* take node n off of the worklist *)
       let instr_n = Int.Map.find_exn cfg.nodes n in
       (* find_exn throws an exception if the key is not found in the map.
        * Because of how this algorithm works, we should always have an input
        * state of some kind for any node we're pulling off the worklist, so if
        * this throws an exception something has gone wrong *)
       let input_n = Int.Map.find_exn inputs n in
       let inputs', worklist' = failwith "Implement me!" in
       work inputs' worklist'
  in
  (* This initializes the inputMap, mapping every variable to Top for the first instruction
     in the code/node in the graph, and mapping every variable to Bot for the rest of the nodes. *)
  let botSigma = initializeSigma (cfg) (Bot) in
  let topSigma = initializeSigma (cfg) (Top) in
  let inputMap = Int.Map.map cfg.nodes ~f:(fun k -> botSigma) in
  let inputMap = Int.Map.set inputMap ~key:1 ~data: topSigma in
 
  (* we use a simple list for the worklist; it's less efficient than various
   * alternatives, but relatively easy to reason about.  You're welcome to use
   * some other datatype if you want, but you're also welcome to just use a list.
   * Your call *)
  work (inputMap) (List.sort (Int.Map.keys cfg.nodes) ~compare:Int.compare)


