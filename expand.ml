type program = exp
and exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | READ
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string

let rec expand : exp -> exp 
=fun e ->
  match e with
  | CONST n -> CONST n
  | VAR x -> VAR x
  | ADD (e1, e2) -> ADD (expand e1, expand e2)
  | SUB (e1, e2) -> SUB (expand e1, expand e2)
  | MUL (e1, e2) -> MUL (expand e1, expand e2)
  | DIV (e1, e2) -> DIV (expand e1, expand e2)
  | ISZERO (e) -> ISZERO (expand e)
  | READ -> READ
  | IF (e1, e2, e3) -> IF (expand e1, expand e2, expand e3)
  | LET (x, e1, e2) ->
    let replaced = replace_all (x, e1) e2
    in if e2 = replaced then LET (x, expand e1, expand e2) else expand replaced
  | LETREC (f, x, e1, e2) -> LETREC (f, x, expand e1, expand e2)
  | PROC (x, e) -> PROC (x, expand e)
  | CALL (e1, e2) -> CALL (expand e1, expand e2)

and replace_all
= fun (x, e) e' ->
  match e' with
  | CONST n -> CONST n
  | VAR v -> if x = v then e else e'
  | ADD (e1, e2) -> ADD (replace_all (x, e) e1, replace_all (x, e) e2)
  | SUB (e1, e2) -> SUB (replace_all (x, e) e1, replace_all (x, e) e2)
  | MUL (e1, e2) -> MUL (replace_all (x, e) e1, replace_all (x, e) e2)
  | DIV (e1, e2) -> DIV (replace_all (x, e) e1, replace_all (x, e) e2)
  | ISZERO (e1) -> ISZERO (replace_all (x, e) e1)
  | READ -> READ
  | IF (e1, e2, e3) -> IF (replace_all (x, e) e1, replace_all (x, e) e2, replace_all (x, e) e3)
  | LET (v, e1, e2) -> if x = v then LET (v, replace_all (x, e) e1, e2) else LET (v, replace_all (x, e) e1, replace_all (x, e) e2)
  | LETREC (f, v, e1, e2) -> if x = f then LETREC (f, v, e1, e2) else if x = v then LETREC (f, v, e1, replace_all (x, e) e2) else LETREC (f, v, replace_all (x, e) e1, replace_all (x, e) e2)
  | PROC (v, e1) -> if x = v then PROC (v, e1) else PROC (v, replace_all (x, e) e1)
  | CALL (e1, e2) -> CALL (replace_all (x, e) e1, replace_all (x, e) e2)
;;
