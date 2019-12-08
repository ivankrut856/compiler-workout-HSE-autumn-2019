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

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = List.init   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> Value.t; l : string -> Value.t; scope : string list}

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

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> 
                    (* Printf.eprintf "%d\n" (Value.to_int @@ List.hd args);  *)
                    (st, i, o @ [Value.to_int @@ List.hd args], None)
    | "$elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String s -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array  a -> List.nth a i
                               )
                    )         
    | "$length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | "$array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))
    | f -> failwith (f ^ " is not a builtin")
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* (* S-expressions      *) | Sexp   of string * t list *)
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    let to_bool x = if x = 0 then false else true
    let to_int (x : bool) : int = if x then 1 else 0

    let to_func op =
      let bti b = if b then 1 else 0 in
      let itb b = b <> 0 in
      let (|>) f g = fun x y -> f (g x y) in
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


    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
    let rec eval env ((st, input, output, ret) as conf) expr : config= 
      match expr with
      | Const n -> (st, input, output, Some (Value.of_int n))
      | Var   x -> (st, input, output, Some (State.eval st x))
      | Binop (op, x, y) -> 
        let conf1 = eval env conf x in
        let (_, _, _, Some Int x_val) = conf1 in
        let conf2 = eval env conf1 y in
        let (st, i, o, Some Int y_val) = conf2 in
        (* let result = bind x_val (fun x -> bind y_val (fun y -> Some (to_func op x y))) in *)
        let result = to_func op x_val y_val in
        (st, i, o, Some Int result)
      | Call (f, args) ->
        (* let (conf1, factual_args) = bind_fold (fun acc item -> let (st, i, o, (Some ret)) as conf = eval env acc item in (conf, ret)) conf args in *)
        let (st, i, o, factual_args) = eval_list env conf args in
        env#definition env f factual_args (st, i, o, None)
      | Array elems -> 
        let (st, i, o, elem_values) = eval_list env conf elems in
        Builtin.eval (st, i, o, None) elem_values "$array"
      | String elems ->
        (st, input, output, Some Value.of_string elems)
      | Elem (x, ind) ->
        let (st, i, o, Some x_val) = eval env conf x in
        let (st, i, o, Some ind_val) = eval env (st, i, o, None) ind in
        Builtin.eval (st, i, o, None) [x_val; ind_val] "$elem"
      | Length x ->
        let (st, i, o, Some x_val) = eval env conf x in
        Builtin.eval (st, i, o, None) [x_val] "$length"
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
             let (_, _, _, Some v) as conf = eval env conf x in
             v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (
      const: x:DECIMAL {Const x};
      var: x:IDENT {Var x};
      call: f:IDENT -"(" args:expr_list -")" {Call (f, args)};

      str_create: s:STRING {String String.sub s 1 ((String.length s) - 2) };
      chr: c:CHAR {Const Char.code c};
      arr_create: -"[" ss:expr_list -"]" {Array ss};
      arr_access: arr:primary -"[" ind:expr -"]" {Elem (arr, ind)};
      length: e:expr -".length" {Length e};

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
      primary: var | const | call | str_create | chr | arr_create | arr_access | length | -"(" expr -")";
      parse: expr
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)

    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let unite_k s1 s2 = match s2 with
    | Skip -> s1
    | otherwise -> Seq (s1, s2)
          
    let rec eval env ((st, i, o, r) as conf) k stm = 
    match stm with
    | Skip -> if k = Skip then conf else eval env conf Skip k
    | Assign (s, inds, e) -> 
      let (st, i, o, ind_values) = Expr.eval_list env conf inds in
      let (st, i, o, Some e_val) = Expr.eval env (st, i, o, None) e in
      let st' = update st s e_val ind_values in
      eval env (st', i, o, None) Skip k
    | Seq (s1, s2) -> 
      eval env conf (unite_k s2 k) s1
    | If (e, s1, s2) ->
      let (st, i, o, Some Int e_val) = Expr.eval env conf e in
      if e_val <> 0 then eval env (st, i, o, None) k s1 else eval env (st, i, o, None) k s2
    | While (e, s) ->
      let (st, i, o, Some Int e_val) = Expr.eval env conf e in
      if e_val <> 0 then eval env (st, i, o, None) (unite_k stm k) s else eval env (st, i, o, None) Skip k
    | Repeat (s, e) -> 
      let (st, i, o, _) as conf1 = eval env conf Skip s in
      let (st1, i1, o1, Some Int e_val) = Expr.eval env conf1 e in
      if e_val = 0 then eval env (st1, i1, o1, None) k stm else eval env (st1, i1, o1, None) Skip k
    | Call (f, args) -> 
      let (st, i, o, factual_args) = Expr.eval_list env conf args in
      let conf2 = env#definition env f factual_args (st, i, o, None) in
      eval env conf2 Skip k
    | Return e -> (match e with
      | None -> conf
      | Some expr ->
        let (st, i, o, Some e_val) = Expr.eval env conf expr in
        (st, i, o, Some e_val)
    )
         
    (* Statement parser *)

    let rec to_if_stm ifs els = match ifs with
    | (e, s)::[] -> (match els with
      | None -> If (e, s, Skip)
      | Some s' -> If (e, s, s')
    )
    | (e, s)::xs -> let rest = to_if_stm xs els in If (e, s, rest)

    ostap (
        expr: !(Expr.expr);
        stmt: assign | if_st | while_st | for_st | repeat_until | call | return | skip;

        (* assign: x:IDENT -":=" y:expr {Assign (x, y)}; *)
        assign: x:IDENT inds:ind_list -":=" y:expr {Assign (x, inds, y)};
        ind_list: (-"[" expr -"]")*;

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
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
