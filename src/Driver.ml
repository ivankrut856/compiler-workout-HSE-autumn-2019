open Ostap

let parse infile =
  let s = Util.read infile in
  Util.parse
    (object
       inherit Matcher.t s
       inherit Util.Lexers.decimal s
       inherit Util.Lexers.ident ["read"; "write"] s
       inherit Util.Lexers.skip [
	 Matcher.Skip.whitespaces " \t\n";
	 Matcher.Skip.lineComment "--";
	 Matcher.Skip.nestedComment "(*" "*)"
       ] s
     end
    )
    (ostap (!(Language.parse) -EOF))

let rec prog_to_str = function
| (x::xs) -> let rest = prog_to_str xs in (
  match x with
  | SM.LD v -> [("LD " ^ v)] @ rest
  | SM.ST v -> [("ST " ^ v)] @ rest
  | SM.BINOP s -> [("BINOP " ^ s)] @ rest
  | SM.CONST x -> [("CONST " ^ (string_of_int x))] @ rest
  | SM.READ -> [("READ ")] @ rest
  | SM.WRITE -> [("WRITE ")] @ rest
)
| [] -> []

let main =
  try
    let interpret  = Sys.argv.(1) = "-i"  in
    let stack      = Sys.argv.(1) = "-s"  in
    let to_compile = not (interpret || stack) in
    let infile     = Sys.argv.(if not to_compile then 2 else 1) in
    match parse infile with
    | `Ok prog ->
      if to_compile
      then 
        let basename = Filename.chop_suffix infile ".expr" in
        Printf.printf "The prog is:\n %s\n" (String.concat "; " (prog_to_str (SM.compile prog)));
        ignore @@ X86.build prog basename
      else 
	let rec read acc =
	  try
	    let r = read_int () in
	    Printf.printf "> ";
	    read (acc @ [r]) 
          with End_of_file -> acc
	in
	let input = read [] in	
	let output = 
	  if interpret 
	  then Language.eval prog input 
	  else SM.run (SM.compile prog) input
	in
	List.iter (fun i -> Printf.printf "%d\n" i) output
    | `Fail er -> Printf.printf "Syntax error: %s" er
  with Invalid_argument _ ->
    Printf.printf "Usage: rc [-i | -s] <input file.expr>\n"
