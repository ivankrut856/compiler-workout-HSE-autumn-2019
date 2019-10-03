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
    (* let eval st expr = failwith "Not yet implemented" *)

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
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | DWhile of Expr.t * t  with show
                                                                    
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
    | Skip -> c
    | If (e, s1, s2) -> (
        match c with
        | (state, input, output) -> if (Expr.eval state e) <> 0 then (eval c s1) else (eval c s2)
    )
    | While (e, s) -> (
        match c with
        | (state, input, output) -> if (Expr.eval state e) <> 0 then let c' = (eval c s) in (eval c' stm) else c
    )
    | DWhile (e, s) -> let (state, input, output) as c' = (eval c s) in (if (Expr.eval state e) == 0 then (eval c' stm) else c')
                               

    let rec to_if_stm ifs els = match ifs with
    | (e, s)::[] -> (match els with
      | None -> If (e, s, Skip)
      | Some s' -> If (e, s, s')
    )
    | (e, s)::xs -> let rest = to_if_stm xs els in If (e, s, rest)

    ostap (
        expr: !(Expr.expr);
        stmt: read | write | assign | if_st | while_st | for_st | repeat_until | skip;
        read: -"read" -"(" x:IDENT -")" {Read x};
        write: -"write" -"(" x:(expr) -")" {Write x};
        assign: x:IDENT -":=" y:(expr) {Assign (x, y)};

        if_st: -"if" e:expr -"then" s:seq elf:elif_st* els:else_st? -"fi" {to_if_stm ((e, s)::elf) els};
        elif_st: -"elif" e:expr -"then" s:seq {(e, s)};
        else_st: -"else" s:seq;

        while_st: -"while" e:expr -"do" s:seq -"od" {While (e, s)};
        for_st: -"for" pre:seq -"," e:expr -"," post:seq -"do" s:seq -"od" {Seq (pre, While (e, Seq (s, post)))};
        repeat_until: -"repeat" s:seq -"until" e:expr {DWhile (e, s)};
        skip: -"skip" {Skip};
        
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
