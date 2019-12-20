open GT       
open Language
open Language.Stmt.Pattern
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p

let rec prt ps_t = match ps_t with
| [] -> ""
| (x::xs) -> (show_insn x) ^ "\n" ^ (prt xs)
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n

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
          
let rec eval env (c : config) p = 
  (* Printf.eprintf "%s <-- Just before the op ST has %d values\n" (if (List.length p) = 0 then "EOP" else (show_insn (List.hd p))) (let (_, stack, _) = c in (List.length stack)); *)
  match p with
  | [] -> c
  | (CONST v)::ps -> let (control_stack, stack, (st, i, o, _)) = c in
                     eval env (control_stack, (Int v)::stack, (st, i, o, None)) ps
  | (BINOP op)::ps -> 
    let (_, t1::t2::_, _) = c in
    (* Printf.eprintf "%s and %s in binop\n" (Value.show_t t1) (Value.show_t t2); *)
    let (control_stack, (Int y)::(Int x)::stack, (st, i, o, _)) = c in 
    eval env (control_stack, (Int (binop_exec op y x))::stack, (st, i, o, None)) ps
  | (LD s)::ps -> let (control_stack, stack, (state, input, output, _)) = c in
                  eval env (control_stack, (Language.State.eval state s)::stack, (state, input, output, None)) ps
  | (ST s)::ps -> let (control_stack, z::stack, (state, input, output, _)) = c in
                  eval env (control_stack, stack, ((Language.State.update s z state), input, output, None)) ps
  | (LABEL l)::ps -> eval env c ps
  | (JMP l)::ps -> (* Printf.printf "jmp %s\n" l; *) eval env c (env#labeled l)
  | (CJMP (cond, l))::ps -> let (control_stack, (Int z)::stack, stm_c) = c in (
    if (z = 0) = (cond = "z") 
    then ((* Printf.printf "cjmp %s\n" l; *) eval env (control_stack, stack, stm_c) (env#labeled l))
    else (eval env (control_stack, stack, stm_c) ps)
  )
  | (END)::ps -> 
    let (cs, _, _) = c in
    if List.length cs = 0 then c else
    let ((ret_prg, ret_state)::control_stack, stack, stm_c) = c in 
    let left_c = let (state, input, output, _) = stm_c in (Language.State.leave state ret_state, input, output, None) in
    eval env (control_stack, stack, left_c) ret_prg
  | (BEGIN (f, args, locals))::ps ->
    let arity = (List.length args) in
    let (control_stack, stack, (state, input, output, _)) = c in
    let (factual_args_rev, new_stack) = split arity stack in
    let factual_args = List.rev factual_args_rev in
    let new_scope = args @ locals in
    let new_state = List.fold_left (fun acc (factual, formal) -> Language.State.update formal factual acc) (Language.State.enter state new_scope) (List.combine factual_args args) in
    eval env (control_stack, new_stack, (new_state, input, output, None)) ps
  | (CALL (f, arity, has_value))::ps ->
    (* Printf.eprintf "%s\n" ("calls " ^ f); *)
    let (cs, stack, (st, i, o, _)) = c in
    if env#is_label f then
      eval env ((ps, st)::cs, stack, (st, i, o, None)) (env#labeled f)
    else
      let (cs, stack, (st, i, o)) = env#builtin (cs, stack, (st, i, o)) f arity (not has_value) in
      eval env (cs, stack, (st, i, o, None)) ps
  | (RET has_value)::ps ->
    let ((ret_prg, ret_state)::control_stack, stack, stm_c) = c in
    let left_c =  let (st, i, o, _) = stm_c in (Language.State.leave st ret_state, i, o, None) in
    eval env (control_stack, stack, left_c) ret_prg
  | (STRING s)::ps ->
    let (cs, st, cfg) = c in
    eval env (cs, (String (Bytes.of_string s)) :: st, cfg) ps
  | (STA (x, n))::ps ->
    let (cs, stack, (st, i, o, _)) = c in 
    let (v::inds, stack') = split (n + 1) stack in
    (* List.iter (fun (Language.Value.Int x) -> Printf.eprintf "%d\n" x) (v::inds); *)
    let st' = Language.Stmt.update st x v (List.rev inds) in
    eval env (cs, stack', (st', i, o, None)) ps
  | DROP::ps ->
    let (cs, z::st, cfg) = c in
    eval env (cs, st, cfg) ps
  | DUP::ps ->
    let (cs, z::st, cfg) = c in
    eval env (cs, z::z::st, cfg) ps
  | SWAP::ps -> 
    let (cs, x::y::st, cfg) = c in
    eval env (cs, y::x::st, cfg) ps
  | (SEXP (tag, n))::ps ->
    let (cs, stack, cfg) = c in
    let (vals, stack') = split n stack in
    eval env (cs, Value.sexp tag (List.rev vals) :: stack', cfg) ps
  | LEAVE :: ps ->
    let (cs, stack, (st, i, o, _)) = c in
    eval env (cs, stack, (State.drop st, i, o, None)) ps
  | (ENTER vars):: ps ->
    let (cs, stack, (st, i, o, _)) = c in
    eval env (cs, stack, (State.push st State.undefined vars, i, o, None)) ps
  | (TAG tag)::ps ->
    let (cs, z::stack, (st, i, o, _)) = c in
    let t = Value.tag_of z in
    eval env (cs, (Value.of_int (if t = tag then 1 else 0)) :: stack, (st, i, o, None)) ps

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
  let (_, _, (_, _, o, _)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           (* Printf.printf "Builtin: %s\n"; *)
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, [], None))
      p
  in
  o

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
    | Expr.Call (f, e) -> let compute_args = List.concat (List.map expr e) in
                          let args_len = List.length e in
                          let call_stmt = [CALL ("L" ^ f, args_len, true)] in
                          compute_args @ call_stmt
    | Expr.Length e -> let compute_e = expr e in
                       let call_stmt = [CALL (".length", 1, true)] in
                       compute_e @ call_stmt
    | Expr.Array elems -> let compute_elems = List.concat (List.map expr elems) in
                          let arr_len = List.length elems in 
                          let call_stmt = [CALL (".array", arr_len, true)] in
                          compute_elems @ call_stmt
    | Expr.String s -> [STRING s]
    | Expr.Elem (x, i) -> expr x @ expr i @ [CALL (".elem", 2, true)]
    | Expr.Sexp (tag, elems) -> let compute_elems = List.concat (List.map expr elems) in
                                let arr_len = List.length elems in
                                let call_stmt = [SEXP (tag, arr_len)] in
                                compute_elems @ call_stmt
    in
    function
    | Stmt.Seq (s1, s2)  -> let _, res1 = compile' (env#set_label "") s1 in 
                            let _, res2 = compile' env s2 in
                            (env, res1 @ res2)
    | Stmt.Assign (x, inds, e) -> (match inds with
      | [] -> (env, expr e @ [ST x])
      | _ -> let compute_inds = List.concat (List.map expr inds) in
             let inds_len = List.length inds in
             (env, compute_inds @ expr e @ [STA (x, inds_len)])
    )
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
                          let args_len = List.length e in
                          let call_stmt = [CALL ("L" ^ f, args_len, false)] in
                          (env, compute_args @ call_stmt)
    | Stmt.Return e -> (match e with
      | None -> (env, [RET false])
      | Some e -> (env, expr e @ [RET true])
    )
    | Stmt.Leave -> (env, [LEAVE])
    | Stmt.Case (e, branches) -> (
      let cur_end_label = env#get_label in
      let (env, end_label) = if cur_end_label = "" then (let str = env#fresh_label in ((env#set_label str), str)) else (env, cur_end_label) in
      let end_label_command = if cur_end_label = "" then [LABEL end_label] else [] in
      (* END LABEL MAGIC ^ *)
      let compute_e = expr e in
      let env, compute_branches =
        let get_by_indices indices = List.flatten (List.map (fun i -> [CONST i; CALL (".elem", 2, true)]) indices) in
        let rec compile_try_match pat indices no_match_case = match pat with
        | Wildcard -> []
        | Ident _ -> []
        | Sexp (tag, elems) -> 
          [DUP] @ (get_by_indices indices) @ [DUP; TAG tag; CJMP ("z", no_match_case);
          DUP; CALL (".length", 1, true); CONST (List.length elems); BINOP ("-"); CJMP ("nz", no_match_case); DROP] @
          List.flatten (
            List.map (
              fun subpat, pat_num ->
                compile_try_match subpat (indices @ [pat_num]) no_match_case
            )
            (List.combine elems (List.init (List.length elems) (fun x -> x))) 
          )
        in
        let rec compile_real_match pat = match pat with
        | Wildcard -> [DROP]
        | Ident x -> [ST x]
        | Sexp (tag, elems) ->
          List.flatten (
            List.map (
              fun subpat, pat_num -> 
                let real_matching_subpat = compile_real_match subpat in
                [DUP; CONST pat_num; CALL (".elem", 2, true)] @ real_matching_subpat
            ) 
            (List.combine elems (List.init (List.length elems) (fun x -> x))) 
          ) @ [DROP]

        in
        let compile_match pat no_match_case = 
          let try_matching = compile_try_match pat [] no_match_case in
          let real_matching = compile_real_match pat in
          try_matching @ [ENTER (vars pat)] @ [DUP] @ real_matching @ [DROP]
        in
        let rec compile_branch env (pat, body) =
          let no_match_case = env#fresh_label in
          let env, compute_body = compile' env body in
          let perform_match = compile_match pat no_match_case in
          (env, perform_match @ compute_body @ [LEAVE] @ [JMP env#get_label] @ [LABEL no_match_case] @ [DROP])
        in
        let rec compile_branches env branches = match branches with
        | [] -> (env, [])
        | b::bs -> let (env, compute_b) = compile_branch env b in let (env, compute_bs) = compile_branches env bs in (env, compute_b @ compute_bs)
        in
        compile_branches env branches
      in
      (env, compute_e @ compute_branches @ end_label_command)
    )

  in 
  compile' env ps

let compile (defs, prg) =
  let start_env = new comp_env in
  let compile_d (f, (args, locals, body)) env =
    let (env, body_code) = compile_p body env in
    let prolog = [LABEL ("L" ^ f); BEGIN ("L" ^ f, args, locals)] in
    let epilog = [END] in
    (env, prolog @ body_code @ epilog)
  in
  let (env, defs_compiled) = List.fold_left (fun (env, acc) def -> let (env', def_compiled) = compile_d def env in (env', acc @ def_compiled)) (start_env, []) defs in
  let (_, main_compiled) = compile_p prg env in
  main_compiled @ [END] @ defs_compiled
