open GT
       
(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)                    
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4;;

(* We need to distinguish the following operand types: *)
@type opnd = 
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)
with show

(* For convenience we define the following synonyms for the registers: *)         
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)                     
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string

(* arithmetic correction: decrement                     *) | Dec   of opnd
(* arithmetic correction: or 0x0001                     *) | Or1   of opnd
(* arithmetic correction: shl 1                         *) | Sal1  of opnd
(* arithmetic correction: shr 1                         *) | Sar1  of opnd
                                                                                                                                   
(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl" 
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s
  | Dec    s           -> Printf.sprintf "\tdecl\t%s" (opnd s)
  | Or1    s           -> Printf.sprintf "\torl\t$0x0001,\t%s" (opnd s)
  | Sal1   s           -> Printf.sprintf "\tsall\t%s" (opnd s)
  | Sar1   s           -> Printf.sprintf "\tsarl\t%s" (opnd s)
                                         
(* Opening stack machine to use instructions without fully qualified names *)
open SM

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)

let is_cmp = function
| "==" -> true
| "!=" -> true
| "<" -> true
| "<=" -> true
| ">" -> true
| ">=" -> true
| otherwise -> false

let is_boolean = function
| "&&" -> true
| "!!" -> true
| otherwise -> false

let to_boolean ptr = 
  [
    Mov (ptr, eax);
    Binop ("cmp", L 0, eax);
    Mov (L 0, eax);
    Set ("ne", "%al");
    Binop ("&&", L 1, eax);
    Mov (eax, ptr);
  ]

let is_div = function
| "%" -> true
| "/" -> true
| otherwise -> false

let suf_of_op = function
| "==" -> "e"
| "!=" -> "ne"
| "<" -> "l"
| "<=" -> "le"
| ">" -> "g"
| ">=" -> "ge"
| otherwise -> failwith "The op is not cmp op"

let perform_call env f arity is_func = 
  let f = if (String.sub f 0 1) = "."
          then "B" ^ String.sub f 1 (String.length f - 1)
          else if (String.sub f 0 1) = "L"
          then "L" ^ String.sub f 1 (String.length f - 1)
          else f
  in
  let args, env = env#pop_some arity in

  let to_save = env#live_registers in
  let regs_save = List.map (fun x -> Push x) to_save in
  let regs_rest = List.map (fun x -> Pop x) (List.rev to_save) in

  
  let args_push = List.map (fun x -> Push x) (List.rev args) in

  let args_push, arity = match f with
  | "Barray" -> (List.rev (Push (L arity) :: args_push)), arity + 1
  | "Bsexp" -> (List.rev (Push (L arity) :: args_push)), arity + 1
  | "Bsta" ->
    let n = arity - 2 in
    let push_s::args_push = List.rev args_push in
    let push_v::args_push = args_push in
    (args_push) @ [push_s; push_v; Push (L n)], arity + 1
  | _ -> (List.rev args_push), arity
  in

  let actual_call = [Call f; Binop ("+", L (4 * arity), esp)] in


  let res, env' = if is_func then env#allocate else (M ("nothing"), env) in
  let save_result = if is_func then [Mov (eax, res)] else [] in
  (env', regs_save @ args_push @ actual_call @ save_result @ regs_rest)

let rec compile env = function 
| [] -> (env, [])
| (p::ps) -> let c_env, c_com = (match p with
  | (CONST x) ->  let ptr, env' = env#allocate in
                  let commands = [Mov ((L x), ptr)] in
                  (env', commands)
  | (LD v) -> let ptr, env' = (env#global v)#allocate in
              let var = (env'#loc v) in
              let commands = match ptr with
              | R n -> [Mov (var, (R n))]
              | s -> [Mov (var, eax); Mov (eax, s)] in
              (env', commands)
  | (ST v) -> let ptr, env' = (env#global v)#pop in
              let var = (env'#loc v) in
              let commands = match ptr with
              | R n -> [Mov ((R n), var)]
              | s -> [Mov (s, eax); Mov (eax, var)] in
              (env', commands)
  | BINOP op when (is_cmp op) -> let y, x, env' = (env#pop2) in
                                 let ptr, env'' = (env'#allocate) in
                                 let commands = [Mov (x, eax); Binop ("cmp", y, eax); Mov (L 0, eax);
                                                 Set (suf_of_op op, "%al"); Binop ("&&", L 1, eax); Mov (eax, ptr)]
                                 in 
                                 (env'', commands)
  
  | BINOP op when (is_div op) -> let y, x, env' = (env#pop2) in
                                 let ptr, env'' = (env'#allocate) in
                                 let commands = [Mov (x, eax); Cltd; IDiv y; Mov ((if op = "/" then eax else edx), ptr)] in
                                 (env'', commands)

  | BINOP op when (is_boolean op) -> let y, x, env' = (env#pop2) in
                                     let ptr, env'' = (env'#allocate) in
                                     let commands = (to_boolean x) @ (to_boolean y) @ [Mov (x, eax); Binop (op, y, eax); Mov (eax, ptr)] in
                                     (env'', commands)
  | BINOP op -> let y, x, env' = (env#pop2) in
                let ptr, env'' = (env'#allocate) in
                let commands = [Mov (x, eax); Binop (op, y, eax); Mov (eax, ptr)] in
                (env'', commands)

  | LABEL l ->  let commands = [Label l] in 
                (env, commands)
  | JMP l -> let commands = [Jmp l] in
             (env, commands)
  | CJMP (cond, l) -> let ptr, env' = (env#pop) in
                      let commands = [Binop ("cmp", L 0, ptr); CJmp (cond, l)] in
                      (env', commands)
  | BEGIN (fname, args, locals) -> let env = (env#enter fname args locals) in
                                   let enter_ins = [Push ebp; Mov (esp, ebp); Binop ("-", M ("$" ^ env#lsize), esp)] in
                                   (env, enter_ins)
  | END -> let commands = [Label env#epilogue; Meta (Printf.sprintf "\t.set\t%s,\t%d" env#lsize (env#allocated * 4)); Mov (ebp, esp); Pop ebp; Ret] in
           (env, commands)
  | CALL (fname, arity, is_func) -> 
    perform_call env fname arity is_func
  | RET is_func -> if is_func then let res, env' = env#pop in (env', [Mov (res, eax); Jmp env#epilogue]) else (env, [Jmp env#epilogue])
  | STRING s ->
    let s, env = env#string s in
    let env = env#push (M ("$" ^ s)) in
    perform_call env ".string" 1 true
  | SEXP (tag, arity) ->
    let env = env#push (L (env#hash tag)) in
    perform_call env ".sexp" (arity + 1) true
  | STA (x, n) ->
    let env = env#push (env#loc x) in
    perform_call env ".sta" (n + 2) false
  | DROP -> failwith "No pattern matching"
  | DUP -> failwith "No pattern matching"
  | SWAP -> failwith "No pattern matching"
  | LEAVE -> failwith "No pattern matching"
  | TAG _ -> failwith "No pattern matching"
  | ENTER _ -> failwith "No pattern matching"

)
             in
             let f_env, f_com = compile c_env ps
             in
             (f_env, c_com @ [Meta ""] @ f_com)

(* A set of strings *)           
module S = Set.Make (String) 

(* A map indexed by strings *)
module M = Map.Make (String) 

(* Environment implementation *)
class env =
  let chars          = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNJPQRSTUVWXYZ" in
  let make_assoc l i = List.combine l (List.init (List.length l) (fun x -> x + i)) in
  let rec assoc  x   = function [] -> raise Not_found | l :: ls -> try List.assoc x l with Not_found -> assoc x ls in
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stringm     = M.empty (* a string map                      *)
    val scount      = 0       (* string count                      *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val static_size = 0       (* static data size                  *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)
    val stackmap    = M.empty (* labels to stack map               *)
    val barrier     = false   (* barrier condition                 *)
                        
    method show_stack =
      GT.show(list) (GT.show(opnd)) stack
             
    method print_locals =
      Printf.printf "LOCALS: size = %d\n" static_size;
      List.iter
        (fun l ->
          Printf.printf "(";
          List.iter (fun (a, i) -> Printf.printf "%s=%d " a i) l;
          Printf.printf ")\n"
        ) locals;
      Printf.printf "END LOCALS\n"

    (* check barrier condition *)
    method is_barrier = barrier

    (* set barrier *)
    method set_barrier = {< barrier = true >}

    (* drop barrier *)
    method drop_barrier = {< barrier = false >}
                            
    (* associates a stack to a label *)
    method set_stack l = (*Printf.printf "Setting stack for %s\n" l;*) {< stackmap = M.add l stack stackmap >}
                               
    (* retrieves a stack for a label *)
    method retrieve_stack l = (*Printf.printf "Retrieving stack for %s\n" l;*)
      try {< stack = M.find l stackmap >} with Not_found -> self
                               
    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->  
        try S (assoc x locals) with Not_found -> M ("global_" ^ x)
        
    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
      	let rec allocate' = function
      	| []                                -> ebx          , 0
      	| (S n)::_                          -> S (n+1)      , n+2
      	| (R n)::_ when n < num_of_regs - 1 -> R (n+1)      , stack_slots
      	| _                                 -> S static_size, static_size+1
      	in
      	allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    method pop_some n = if n == 0 then ([], self) 
                    else let (el, env') = self#pop in
                         let (els, env'') = env'#pop_some (n - 1) in
                         (el::els, env'')

    (* peeks the top of the stack (the stack does not change) *)
    method peek = List.hd stack

    (* peeks two topmost values from the stack (the stack itself does not change) *)
    method peek2 = let x::y::_ = stack in x, y

    (* tag hash: gets a hash for a string tag *)
    method hash tag =
      let h = Pervasives.ref 0 in
      for i = 0 to min (String.length tag - 1) 4 do
        h := (!h lsl 6) lor (String.index chars tag.[i])
      done;
      !h      
             
    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* registers a string constant *)
    method string x =
      try M.find x stringm, self
      with Not_found ->
        let y = Printf.sprintf "string_%d" scount in
        let m = M.add x y stringm in
        y, {< scount = scount + 1; stringm = m>}
                       
    (* gets all global variables *)      
    method globals = S.elements globals

    (* gets all string definitions *)      
    method strings = M.bindings stringm

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots                                
                                
    (* enters a function *)
    method enter f a l =
      let n = List.length l in
      {< static_size = n; stack_slots = n; stack = []; locals = [make_assoc l 0]; args = make_assoc a 0; fname = f >}

    (* enters a scope *)(* 
    method scope vars =
      let n = List.length vars in
      let static_size' = n + static_size in
      {< stack_slots = max stack_slots static_size'; static_size = static_size'; locals = (make_assoc vars static_size) :: locals >} *)

    (* leaves a scope *)(* 
    method unscope =
      let n = List.length (List.hd locals) in
      {< static_size = static_size - n; locals = List.tl locals >} *)
        
    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname
                                     
    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    (* method live_registers depth =
      let rec inner d acc = function
      | []             -> acc
      | (R _ as r)::tl -> inner (d+1) (if d >= depth then (r::acc) else acc) tl
      | _::tl          -> inner (d+1) acc tl
      in
      inner 0 [] stack *)

    method live_registers =
      List.filter (function R _ -> true | _ -> false) stack
       
  end
  
(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Call ("raw", [Language.Expr.Const 0])))) in
  let sm_code = ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt)) in
  (* print_prg sm_code; *)
  let env, code =
    compile
      (new env)
      sm_code
  in
  let data = Meta "\t.data" :: (List.map (fun s      -> Meta (Printf.sprintf "%s:\t.int\t0"         s  )) env#globals) @
                               (List.map (fun (s, v) -> Meta (Printf.sprintf "%s:\t.string\t\"%s\"" v s)) env#strings) in 
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -g3 -o %s %s/runtime.o %s.s" name inc name)
 
