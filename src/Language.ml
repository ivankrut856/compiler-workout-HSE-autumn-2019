(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap

(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

  end
    
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
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                    

    
    let to_bool x = if x = 0 then false else true
    let to_int (x : bool) : int = if x then 1 else 0

                                   
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (
      const: x:DECIMAL {Const x};
      var: x:IDENT {Var x};

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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)

    let rec eval env (c : config) (stm : t) : config = 
    match stm with
    | Seq (s1, s2) -> eval env (eval env c s1) s2
    | Assign (s, exp) -> (
        match c with
        | (state, input, output) -> ((State.update s (Expr.eval state exp) state), input, output)
    )
    | Read s -> (
        match c with
        | (state, z :: input, output) -> ((State.update s z state), input, output)
        | _ -> failwith (Printf.sprintf "Unexpected end of file")
    )
    | Write exp -> (
        match c with
        | (state, input, output) -> (state, input, output@[(Expr.eval state exp)])
    )
    | Skip -> c
    | If (e, s1, s2) -> (
        match c with
        | (state, input, output) -> if (Expr.eval state e) <> 0 then (eval env c s1) else (eval env c s2)
    )
    | While (e, s) -> (
        match c with
        | (state, input, output) -> if (Expr.eval state e) <> 0 then let c' = (eval env c s) in (eval env c' stm) else c
    )
    | Repeat (s, e) -> let (state, input, output) as c' = (eval env c s) in (if (Expr.eval state e) == 0 then (eval env c' stm) else c')
    | Call (f, factual_args) -> let (state, input, output) = c in
                                let (formal_args, locals, body) = env#definition f in
                                let scope = (locals @ formal_args) in
                                let scoped_state = State.push_scope state scope in
                                let function_state = List.fold_left (fun acc (factual, formal) -> State.update formal (Expr.eval state factual) acc) scoped_state (List.combine factual_args formal_args) in
                                let (state', input', output') = eval env (function_state, input, output) body in
                                (State.drop_scope state' state, input', output')

                          

    let rec to_if_stm ifs els = match ifs with
    | (e, s)::[] -> (match els with
      | None -> If (e, s, Skip)
      | Some s' -> If (e, s, s')
    )
    | (e, s)::xs -> let rest = to_if_stm xs els in If (e, s, rest)

    ostap (
        expr: !(Expr.expr);
        stmt: read | write | assign | if_st | while_st | for_st | repeat_until | call | skip;
        read: -"read" -"(" x:IDENT -")" {Read x};
        write: -"write"  -"(" x:(expr) -")" {Write x};
        assign: x:IDENT -":=" y:(expr) {Assign (x, y)};

        if_st: -"if" e:expr -"then" s:seq elf:elif_st* els:else_st? -"fi" {to_if_stm ((e, s)::elf) els};
        elif_st: -"elif" e:expr -"then" s:seq {(e, s)};
        else_st: -"else" s:seq;

        while_st: -"while" e:expr -"do" s:seq -"od" {While (e, s)};
        for_st: -"for" pre:seq -"," e:expr -"," post:seq -"do" s:seq -"od" {Seq (pre, While (e, Seq (s, post)))};
        repeat_until: -"repeat" s:seq -"until" e:expr {Repeat (s, e)};

        call: f:IDENT -"(" args:expr* -")" {Call (f, args)};

        skip: -"skip" {Skip}; 

        seq: <s::ss> : !(Util.listBy)[ostap (";")][stmt] {List.fold_left (fun ss s -> Seq (ss, s)) s ss};
        parse: seq

    )
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (                                      
      
      def: -"fun" f:IDENT -"(" args:ident_list -")" locals:local -"{" body:!(Stmt.parse) -"}" {(f, (args, locals, body))};
      local: -"local" ident_list | "" {[]} ;
      ident_list: !(Util.listBy)[ostap (",")][ident] | "" {[]} ;
      ident: IDENT;

      parse: def
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
