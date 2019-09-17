open GT
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         

let binop_exec (op : string) (y : int) (x : int) : int = match op with
	| "!!" -> Syntax.Expr.to_int ((Syntax.Expr.to_bool x) || (Syntax.Expr.to_bool y))
	| "&&" -> Syntax.Expr.to_int ((Syntax.Expr.to_bool x) && (Syntax.Expr.to_bool y))
	| "==" -> Syntax.Expr.to_int (x = y)
	| "!=" -> Syntax.Expr.to_int (x <> y)
	| "<" -> Syntax.Expr.to_int (x < y)
	| ">" -> Syntax.Expr.to_int (x > y)
	| "<=" -> Syntax.Expr.to_int (x <= y)
	| ">=" -> Syntax.Expr.to_int (x >= y)
	| "+" -> x + y
	| "-" -> x - y
	| "*" -> x * y
	| "/" -> x / y
	| "%" -> x mod y
	| _ -> failwith "Incorrect binop code"

let rec exec (c : config) (order : insn) : config = match order, c with
	| CONST v, (stack, synconf) -> (v :: stack, synconf)
	| BINOP op, (y :: x :: stack, synconf) -> ((binop_exec op y x) :: stack, synconf)
	| BINOP op, _ -> failwith "There are no two needed values on the stack"
	| READ, (stack, (state, z :: input, output)) -> (z :: stack, (state, input, output))
	| READ, _ -> failwith "Unexpected end of file"
	| WRITE, (z :: stack, (state, input, output)) -> (stack, (state, input, output @ [z]))
	| WRITE, _ -> failwith "Empty stack on write operation"
	| LD s, (stack, (state, input, output)) -> ((state s) :: stack, (state, input, output))
	| ST s, (z :: stack, (state, input, output)) -> (stack, ((Syntax.Expr.update s z state), input, output))
	| ST s, _ -> failwith "Empty stack on store operation"



let rec eval c p = List.fold_left exec c p

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile_exp (exp : Syntax.Expr.t) : prg = match exp with
	| Const x -> [CONST x]
	| Var s -> [LD s]
	| Binop (op, e1, e2) -> (compile_exp e1) @ (compile_exp e2) @ [BINOP op]

let rec compile (stm : Syntax.Stmt.t) : prg = match stm with
	| Seq (s1, s2) -> (compile s1) @ (compile s2)
	| Read s -> [READ; (ST s)]
	| Write exp -> (compile_exp exp) @ [WRITE]
	| Assign (s, exp) -> (compile_exp exp) @ [ST s]
