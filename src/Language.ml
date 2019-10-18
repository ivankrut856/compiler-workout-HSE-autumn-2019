(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let bind (o : 'a option) (f : 'a -> 'b option) : 'b option = match o with
| None -> None
| Some v -> f v

let rec bind_fold (f : 'a -> 'b -> 'a * 'c) (acc : 'a) (items : 'b list) : 'a * 'c list = match items with
| [] -> (acc, [])
| x::xs -> 
  let (new_acc, new_x) = f acc x in
  let (end_acc, end_xs) = bind_fold f new_acc xs in
  (end_acc, new_x::end_xs)

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
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    let to_bool x = if x = 0 then false else true
    let to_int (x : bool) : int = if x then 1 else 0

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
    *)                                   



    let to_func op =
      let bti b = if b then 1 else 0 in
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
    
    let rec eval env ((st, input, output, ret) as conf) expr : config =      
      match expr with
      | Const n -> (st, input, output, Some n)
      | Var   x -> (st, input, output, Some (State.eval st x))
      | Binop (op, x, y) -> 
        let conf1 = eval env conf x in
        let (_, _, _, x_val) = conf1 in
        let conf2 = eval env conf1 y in
        let (st, i, o, y_val) = conf2 in
        let result = bind x_val (fun x -> bind y_val (fun y -> Some (to_func op x y))) in
        (st, i, o, result)
      | Call (f, args) ->
        let (conf1, factual_args) = bind_fold (fun acc item -> let (st, i, o, (Some ret)) as conf = eval env acc item in (conf, ret)) conf args in
        env#definition env f factual_args conf1
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)

    ostap (
      const: x:DECIMAL {Const x};
      var: x:IDENT {Var x};
      call: f:IDENT -"(" args:expr_list -")" {Call (f, args)};
      expr_list: !(Util.list0By)[ostap (",")][expr];
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
      primary: var | const | call | -"(" expr -")";
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
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> k -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    (* let rec eval env ((st, i, o, r) as conf) k stmt = failwith "Not implemnted" *)

    let unite_k s1 s2 = match s2 with
    | Skip -> s1
    | otherwise -> Seq (s1, s2)

    let rec eval env ((st, i, o, r) as conf) k stm = 
    match stm with
    | Skip -> if k = Skip then conf else eval env conf Skip k
    | Assign (s, e) -> 
      let (st, i, o, (Some e_val)) = Expr.eval env conf e in
      eval env (State.update s e_val st, i, o, None) Skip k
    | Read s -> 
      let (st, z::i, o, _) = conf in
      eval env (State.update s z st, i, o, None) Skip k
    | Write e -> 
      let (st, i, o, (Some e_val)) = Expr.eval env conf e in
      eval env (st, i, o @ [e_val], None) Skip k
    | Seq (s1, s2) -> 
      eval env conf (unite_k s2 k) s1
    | If (e, s1, s2) ->
      let (st, i, o, Some e_val) = Expr.eval env conf e in
      if e_val <> 0 then eval env (st, i, o, None) k s1 else eval env (st, i, o, None) k s2
    | While (e, s) ->
      let (st, i, o, Some e_val) = Expr.eval env conf e in
      if e_val <> 0 then eval env (st, i, o, None) (unite_k stm k) s else eval env (st, i, o, None) Skip k
    | Repeat (s, e) -> 
      let (st, i, o, _) as conf1 = eval env conf Skip s in
      let (st1, i1, o1, Some e_val) = Expr.eval env conf1 e in
      if e_val = 0 then eval env (st1, i1, o1, None) k stm else eval env (st1, i1, o1, None) Skip k
    | Call (f, args) -> 
      let (conf1, factual_args) = bind_fold (fun acc item -> let (st, i, o, (Some ret)) as conf = Expr.eval env acc item in (conf, ret)) conf args in
      let conf2 = env#definition env f factual_args conf1 in
      eval env conf2 Skip k
    | Return e -> (match e with
      | None -> conf
      | Some expr ->
        let (st, i, o, Some e_val) = Expr.eval env conf expr in
        (st, i, o, Some e_val)
    )



    let rec to_if_stm ifs els = match ifs with
    | (e, s)::[] -> (match els with
      | None -> If (e, s, Skip)
      | Some s' -> If (e, s, s')
    )
    | (e, s)::xs -> let rest = to_if_stm xs els in If (e, s, rest)
         
    (* Statement parser *)
    ostap (
        expr: !(Expr.expr);
        stmt: read | write | assign | if_st | while_st | for_st | repeat_until | call | return | skip;
        read: -"read" -"(" x:IDENT -")" {Read x};
        write: -"write"  -"(" x:expr -")" {Write x};
        assign: x:IDENT -":=" y:expr {Assign (x, y)};

        if_st: -"if" e:expr -"then" s:seq elf:elif_st* els:else_st? -"fi" {to_if_stm ((e, s)::elf) els};
        elif_st: -"elif" e:expr -"then" s:seq {(e, s)};
        else_st: -"else" s:seq;

        while_st: -"while" e:expr -"do" s:seq -"od" {While (e, s)};
        for_st: -"for" pre:seq -"," e:expr -"," post:seq -"do" s:seq -"od" {Seq (pre, While (e, Seq (s, post)))};
        repeat_until: -"repeat" s:seq -"until" e:expr {Repeat (s, e)};

        call: f:IDENT -"(" args:!(Expr.expr_list) -")" {Call (f, args)};
        return: -"return" x:expr? {Return x};

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
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =                                                                      
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
