(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap
       
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
     *)                                          
    let to_bool x = if x = 0 then false else true
    let to_int (x : bool) : int = if x then 1 else 0

    let rec eval (s : state) (e : t) : int = 
        match e with
        | Const x -> x
        | Var x -> s x
        | Binop ("!!", e1, e2) -> to_int ((to_bool @@ eval s e1) || (to_bool @@ eval s e2))
        | Binop ("&&", e1, e2) -> to_int ((to_bool @@ eval s e1) && (to_bool @@ eval s e2))
        | Binop ("==", e1, e2) -> to_int ((eval s e1) = (eval s e2))
        | Binop ("!=", e1, e2) -> to_int ((eval s e1) <> (eval s e2))
        | Binop ("<", e1, e2) -> to_int ((eval s e1) < (eval s e2))
        | Binop (">", e1, e2) -> to_int ((eval s e1) > (eval s e2))
        | Binop ("<=", e1, e2) -> to_int ((eval s e1) <= (eval s e2))
        | Binop (">=", e1, e2) -> to_int ((eval s e1) >= (eval s e2))
        | Binop ("+", e1, e2) -> (eval s e1) + (eval s e2)
        | Binop ("-", e1, e2) -> (eval s e1) - (eval s e2)
        | Binop ("*", e1, e2) -> (eval s e1) * (eval s e2)
        | Binop ("/", e1, e2) -> (eval s e1) / (eval s e2)
        | Binop ("%", e1, e2) -> (eval s e1) mod (eval s e2)
        | _ -> failwith (Printf.sprintf "Incorrect BINOP")

    (* Expression parser. You can use the following terminals:
         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)

    ostap (
        const: x:DECIMAL {Const x};
        var: x:IDENT {Var x};
        (* binop: a:expr x:op b:expr {Binop (Token.repr x, a, b)}; *)
        (* op: ("!!" | "&&" | "==" | "!=" | "<" | ">" | "<=" | ">=" | "+" | "-" | "*" | "/" | "%"); *)
        (* expr: binop | const | var; *)

        expr: 
            !(Util.expr
                (fun x -> x)
                [|
                    `Lefta, [
                              ostap("!!"), (fun x y -> Binop ("!!", x, y))
                            ];
                    `Lefta, [
                              ostap("&&"), (fun x y -> Binop ("&&", x, y))
                            ];
                    `Nona,  [
                              ostap("=="), (fun x y -> Binop ("==", x, y));
                              ostap("!="), (fun x y -> Binop ("!=", x, y));
                              ostap("<="), (fun x y -> Binop ("<=", x, y));
                              ostap("<"),  (fun x y -> Binop ("<", x, y));
                              ostap(">="), (fun x y -> Binop (">=", x, y));
                              ostap(">"),  (fun x y -> Binop (">", x, y))
                            ];
                    `Lefta, [
                              ostap("+"), (fun x y -> Binop ("+", x, y));
                              ostap("-"), (fun x y -> Binop ("-", x, y))
                            ];
                    `Lefta, [
                              ostap("*"), (fun x y -> Binop ("*", x, y));
                              ostap("%"), (fun x y -> Binop ("%", x, y));
                              ostap("/"), (fun x y -> Binop ("/", x, y))
                            ];
                    (* `Righta, []; *)
                |]
                primary
            );
        primary: var | const | -"(" expr -")";
        parse: expr
    )

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)

    let rec eval (c : config) (stm : t) : config = 
    match stm with
    | Seq (s1, s2) -> eval (eval c s1) s2
    | Assign (s, exp) -> (
        match c with
        | (state, input, output) -> ((Expr.update s (Expr.eval state exp) state), input, output)
    )
    | Read s -> (
        match c with
        | (state, z :: input, output) -> ((Expr.update s z state), input, output)
        | _ -> failwith (Printf.sprintf "Unexpected end of file")
    )
    | Write exp -> (
        match c with
        | (state, input, output) -> (state, input, output@[(Expr.eval state exp)])
    )

    (* let from_seq_list (x:'a) : t = failwith "kek" *)

    (* Statement parser *)
    ostap (
        expr: !(Expr.expr);
        stmt: read | write | assign;
        read: -"read" -"(" x:IDENT -")" {Read x};
        write: -"write" -"(" x:(expr) -")" {Write x};
        assign: x:IDENT -":=" y:(expr) {Assign (x, y)};
        (* seq: x:stmt -";" y:stmt {Seq (x, y)}; *)
        seq: <s::ss> : !(Util.listBy)[ostap (";")][stmt] {List.fold_left (fun ss s -> Seq (ss, s)) s ss};
        parse: seq
    )

      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
