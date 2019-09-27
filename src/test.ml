open GT
open Ostap.Combinators

let _ = 
ostap (
    "a"
(* 
    expr: (x:const) | (x:var) | (x:binop);
    const: DECIMAL;
    var: IDENT; 
    binop: expr op expr;
    op: "+";
    parse: expr; *)
)