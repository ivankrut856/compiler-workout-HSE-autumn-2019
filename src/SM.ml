open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)

let rec prt ps_t = match ps_t with
| [] -> ""
| (x::xs) -> (show_insn x) ^ "\n" ^ (prt xs)

let binop_exec (op : string) (y : int) (x : int) : int = match op with
    | "!!" -> Language.Expr.to_int ((Language.Expr.to_bool x) || (Language.Expr.to_bool y))
    | "&&" -> Language.Expr.to_int ((Language.Expr.to_bool x) && (Language.Expr.to_bool y))
    | "==" -> Language.Expr.to_int (x = y)
    | "!=" -> Language.Expr.to_int (x <> y)
    | "<" -> Language.Expr.to_int (x < y)
    | ">" -> Language.Expr.to_int (x > y)
    | "<=" -> Language.Expr.to_int (x <= y)
    | ">=" -> Language.Expr.to_int (x >= y)
    | "+" -> x + y
    | "-" -> x - y
    | "*" -> x * y
    | "/" -> x / y
    | "%" -> x mod y
    | _ -> failwith "Incorrect binop code"

let exec (c : config) (order : insn) : config = (* (Printf.printf "%s\n" (show_insn order)); *) 
  match order, c with
    | CONST v, (control_stack, stack, synconf) -> (control_stack, v :: stack, synconf)
    | BINOP op, (control_stack, y :: x :: stack, synconf) -> (control_stack, (binop_exec op y x) :: stack, synconf)
    | BINOP op, _ -> failwith "There are no two needed values on the stack"
    | READ, (control_stack, stack, (state, z :: input, output)) -> (control_stack, z :: stack, (state, input, output))
    | READ, _ -> failwith "Unexpected end of file"
    | WRITE, (control_stack, z :: stack, (state, input, output)) -> (control_stack, stack, (state, input, output @ [z]))
    | WRITE, _ -> failwith "Empty stack on write operation"
    | LD s, (control_stack, stack, (state, input, output)) -> (control_stack, (Language.State.eval state s) :: stack, (state, input, output))
    | ST s, (control_stack, z :: stack, (state, input, output)) -> (control_stack, stack, ((Language.State.update s z state), input, output))
    | ST s, _ -> failwith "Empty stack on store operation"
    | otherwise -> failwith "Attempt to exec control instruction"


let split list n =
    let rec aux i acc = function
      | [] -> List.rev acc, []
      | h :: t as l -> if i = 0 then List.rev acc, l
                       else aux (i-1) (h :: acc) t  in
    aux n [] list
(* 
let head_or_d list d = match list with
| [] -> d
| (x::xs) -> x *)

let head (x::xs) = x

let rec eval env c p = (* Printf.eprintf "%s\n" (if (List.length p) = 0 then "EOP" else (show_insn (head p))); *)
match p with
| [] -> c
| (LABEL l)::ps -> eval env c ps
| (JMP l)::ps -> (* Printf.printf "jmp %s\n" l; *) eval env c (env#labeled l)
| (CJMP (cond, l))::ps -> let (control_stack, z::stack, stm_c) = c in (
  if (z = 0) = (cond = "z") 
  then ((* Printf.printf "cjmp %s\n" l; *) eval env (control_stack, stack, stm_c) (env#labeled l))
  else (eval env (control_stack, stack, stm_c) ps)
)
| (END)::ps -> 
  let ((ret_prg, ret_state)::control_stack, stack, stm_c) = c in 
  let left_c = let (state, input, output) = stm_c in (Language.State.drop_scope state ret_state, input, output) in
  eval env (control_stack, stack, left_c) ret_prg
| (BEGIN (args, locals))::ps ->
  let arity = (List.length args) in
  let (control_stack, stack, (state, input, output)) = c in
  let (factual_args_rev, new_stack) = split stack arity in
  let factual_args = List.rev factual_args_rev in
  let new_scope = args @ locals in
  let new_state = List.fold_left (fun acc (factual, formal) -> Language.State.update formal factual acc) (Language.State.push_scope state new_scope) (List.combine factual_args args) in
  eval env (control_stack, new_stack, (new_state, input, output)) ps
| (CALL f)::ps ->
  let (control_stack, stack, (state, input, output)) = c in
  eval env ((ps, state)::control_stack, stack, (state, input, output)) (env#labeled f)
| inst::ps -> let c' = exec c inst in eval env c' ps

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let start_env = object method labeled l = M.find l m end in
  let (_, _, (_, _, o)) = eval start_env ([], [], (State.empty, i, [])) (start_env#labeled "func_main") in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)



class comp_env =
  object(self)
    val cnt : int ref = Base.ref 0
    val end_label : string = ""

    method fresh_label = cnt := (!cnt) + 1; "label_" ^ (string_of_int (!cnt))

    method get_label = end_label
    method set_label s = {< end_label = s >}

  end

let rec compile_p (ps : Stmt.t) (env : comp_env) =
  let rec compile' (env : comp_env) =
    let rec expr = function
    | Expr.Var   x          -> [LD x]
    | Expr.Const n          -> [CONST n]
    | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
    in
    function
    | Stmt.Seq (s1, s2)  -> let _, res1 = compile' (env#set_label "") s1 in 
                            let _, res2 = compile' env s2 in
                            (env, res1 @ res2)
    | Stmt.Read x        -> (env, [READ; ST x])
    | Stmt.Write e       -> (env, expr e @ [WRITE])
    | Stmt.Assign (x, e) -> (env, expr e @ [ST x])
    | Stmt.Skip          -> (env, [])
    | Stmt.Repeat (s, e) -> let new_label = env#fresh_label in
                            let _, res = compile' env s in
                            (env, [LABEL new_label] @ res @ expr e @ [CJMP ("z", new_label)]) 
    | Stmt.While (e, s) -> let new_label1 = env#fresh_label in
                           let new_label2 = env#fresh_label in
                           let _, res = compile' env s in
                           (env, [LABEL new_label1] @ expr e @ [CJMP ("z", new_label2)] @ res @ [JMP new_label1; LABEL new_label2])
    | Stmt.If (e, s1, s2) -> let true_label = env#fresh_label in
                             let cur_end_label = env#get_label in
                             let env', end_label = if cur_end_label = ""
                                                   then (let str = env#fresh_label in
                                                   ((env#set_label str), str))
                                                   else (env, cur_end_label) in
                             let env'', res1 = compile' env' s1 in
                             let env3d, res2 = compile' env'' s2 in
                             let end_label_command = if cur_end_label = "" then [LABEL end_label] else [] in
                             (env3d, expr e @ [CJMP ("nz", true_label)] @ res2 @ [JMP end_label; LABEL true_label] @ res1 @ end_label_command)
    | Stmt.Call (f, e) -> let compute_args = List.concat (List.map (expr) e) in
                          let call_stmt = [CALL ("func_" ^ f)] in
                          (env, compute_args @ call_stmt)


  in 
  compile' (env) ps



let compile (defs, prg) =
  let start_env = new comp_env in
  let compile_d (f, (args, locals, body)) env =
    let (env, body_code) = compile_p body env in
    let prolog = [LABEL ("func_" ^ f); BEGIN (args, locals)] in
    let epilog = [END] in
    (env, prolog @ body_code @ epilog)
  in
  let (env, defs_compiled) = List.fold_left (fun (env, acc) def -> let (env', def_compiled) = compile_d def env in (env', acc @ def_compiled)) (start_env, []) defs in
  let (_, main_compiled) = compile_p prg env in
  defs_compiled @ [LABEL "func_main"] @ main_compiled
