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
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
(* let rec eval env conf prog = failwith "Not yet implemented" *)
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

let exec (c : config) (order : insn) : config = (* (Printf.printf "%s\n" (show_insn order)); *) match order, c with
    | CONST v, (stack, synconf) -> (v :: stack, synconf)
    | BINOP op, (y :: x :: stack, synconf) -> ((binop_exec op y x) :: stack, synconf)
    | BINOP op, _ -> failwith "There are no two needed values on the stack"
    | READ, (stack, (state, z :: input, output)) -> (z :: stack, (state, input, output))
    | READ, _ -> failwith "Unexpected end of file"
    | WRITE, (z :: stack, (state, input, output)) -> (stack, (state, input, output @ [z]))
    | WRITE, _ -> failwith "Empty stack on write operation"
    | LD s, (stack, (state, input, output)) -> ((state s) :: stack, (state, input, output))
    | ST s, (z :: stack, (state, input, output)) -> (stack, ((Language.Expr.update s z state), input, output))
    | ST s, _ -> failwith "Empty stack on store operation"
    | otherwise -> failwith "Attempt to exec control instruction"


let rec prt ps_t = match ps_t with
| [] -> ""
| (x::xs) -> (show_insn x) ^ "\n" ^ (prt xs)

let rec eval env c p = match p with
| [] -> c
| (LABEL l)::ps -> eval env c ps
| (JMP l)::ps -> (* Printf.printf "jmp %s\n" l; *) eval env c (env#labeled l)
| (CJMP (cond, l))::ps -> let (z::stack, stm_c) = c in (if (z = 0) = (cond = "z") 
                                                        then ((* Printf.printf "cjmp %s\n" l; *) eval env (stack, stm_c) (env#labeled l))
                                                        else (eval env (stack, stm_c) ps))
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
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

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

let rec compile (ps : Stmt.t) =
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
    | Stmt.DWhile (e, s) -> let new_label = env#fresh_label in
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

                             
  in 
  let env, res = compile' (new comp_env) ps in res
