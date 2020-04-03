type program = exp
and exp = 
  | UNIT
  | TRUE
  | FALSE
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | NIL
  | CONS of exp * exp      
  | APPEND of exp * exp
  | HEAD of exp
  | TAIL of exp
  | ISNIL of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | LETMREC of (var * var * exp) * (var * var * exp) * exp
  | PROC of var * exp
  | CALL of exp * exp
  | PRINT of exp
  | SEQ of exp * exp
and var = string

type value = 
  | Unit 
  | Int of int 
  | Bool of bool 
  | List of value list
  | Procedure of var * exp * env 
  | RecProcedure of var * var * exp * env
  | MRecProcedure of var * var * exp * var * var * exp * env
and env = (var * value) list

let rec string_of_value v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | List lst -> "[" ^ List.fold_left (fun s x -> s ^ ", " ^ x) "" (List.map string_of_value lst) ^ "]"
  | _ -> "(functional value)"

exception UndefinedSemantics

let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec lookup_env x e = 
  match e with
  | [] -> raise (Failure ("variable " ^ x ^ " is not bound in env")) 
  | (y,v)::tl -> if x = y then v else lookup_env x tl

let rec eval : exp -> env -> value
=fun exp env ->
  match exp with
  | PRINT e -> (print_endline (string_of_value (eval e env)); Unit)
  | UNIT -> Unit
  | TRUE -> Bool true
  | FALSE -> Bool false
  | CONST n -> Int n
  | VAR x -> lookup_env x env
  | ADD (e1, e2) -> binary_int_operator (+) e1 e2 env
  | SUB (e1, e2) -> binary_int_operator (-) e1 e2 env
  | MUL (e1, e2) -> binary_int_operator (fun x y -> x * y) e1 e2 env
  | DIV (e1, e2) -> binary_int_operator (/) e1 e2 env
  | EQUAL (e1, e2) -> (
    match (eval e1 env), (eval e2 env) with
      | Int n1, Int n2 -> if n1 = n2 then Bool true else Bool false
      | Bool p1, Bool p2 -> if p1 = p2 then Bool true else Bool false
      | _ -> raise (Failure "Undefined Semantics")
  )
  | LESS (e1, e2) -> (
    match (eval e1 env), (eval e2 env) with
      | Int n1, Int n2 -> if n1 < n2 then Bool true else Bool false
      | _ -> raise (Failure "Undefined Semantics")
  )
  | NOT e -> (
    match eval e env with
      | Bool p -> Bool (not p)
      | _ -> raise (Failure "Undefined Semantics")
  )
  | NIL -> List []
  | CONS (e1, e2) -> (
    match (eval e1 env), (eval e2 env) with
      | v, List lst -> List (v::lst)
      | _ -> raise (Failure "Undefined Semantics")
  )
  | APPEND (e1, e2) -> (
    match (eval e1 env), (eval e2 env) with
      | List lst1, List lst2 -> List (lst1@lst2)
      | _ -> raise (Failure "Undefined Semantics")
  )
  | HEAD e -> (
    match (eval e env) with
      | List (hd::tl) -> hd
      | _ -> raise (Failure "Undefined Semantics")
  )
  | TAIL e -> (
    match (eval e env) with
      | List (hd::tl) -> List tl
      | _ -> raise (Failure "Undefined Semantics")
  )
  | ISNIL e -> (
    match (eval e env) with
      | List [] -> Bool true
      | List (hd::tl) -> Bool false
      | _ -> raise (Failure "Undefined Semantics")
  )
  | IF (e1, e2, e3) -> (
    match (eval e1 env) with
      | Bool true -> (eval e2 env)
      | Bool false -> (eval e3 env)
      | _ -> raise (Failure "Undefined Semantics")
  )
  | LET (x, e1, e2) ->
    let v1 = eval e1 env in
    let v = eval e2 (extend_env (x,v1) env)
    in v
  | LETREC (f, x, e1, e2) -> eval e2 (extend_env (f,RecProcedure(f,x,e1,env)) env)
  | LETMREC ((f, x, e1), (g, y, e2), e3) -> eval e3 (extend_env (g,MRecProcedure(g,y,e2,f,x,e1,env)) (extend_env (f,MRecProcedure(f,x,e1,g,y,e2,env)) env))
  | PROC (x, e) -> Procedure (x, e, env)
  | CALL (e1, e2) -> (
    match (eval e1 env) with
      | Procedure (x, e, env') -> (
        let v = eval e2 env in
        let v' = eval e (extend_env (x,v) env')
        in v'
      )
      | RecProcedure (f, x, e, env') -> (
        let v = eval e2 env in
        let v' = eval e (extend_env (x,v) (extend_env (f,RecProcedure (f,x,e,env')) env'))
        in v'
      )
      | MRecProcedure (f, x, e1', g, y, e2', env') -> (
        let v = eval e2 env in
        let v' = eval e1' (extend_env (x,v) (extend_env (f,MRecProcedure(f,x,e1',g,y,e2',env')) (extend_env (g,MRecProcedure(g,y,e2',f,x,e1',env')) env')))
        in v'
      )
      | _ -> raise (Failure "Undefined Semantics")
  )
  | SEQ (e1, e2) -> (
    match (eval e1 env) with
      | _ -> eval e2 env
  )

and binary_int_operator : (int -> int -> int) -> exp -> exp -> env -> value
=fun op e1 e2 env ->
  match (eval e1 env), (eval e2 env) with
    | Int n1, Int n2 -> Int (op n1 n2)
    | _ -> raise (Failure "Undefined Semantics")

let runml : program -> value
=fun pgm -> eval pgm empty_env
;;

(* 1+3 *)
runml(ADD(CONST 1,CONST 3)) = Int 4;;

(* if (not false) then 1 else 2 *)
runml(IF(NOT FALSE,CONST 1,CONST 2)) = Int 1;;

(* if 0 then true else false *)
(*runml(IF(CONST 0,TRUE,FALSE));;*)

(* 3*2 < 5 *)
runml(LESS(MUL(CONST 3, CONST 2),CONST 5)) = Bool false;;

(* true = 0 *)
(*runml(EQUAL(TRUE,CONST 0));;*)

(* tail((1::[])@(2::3::[])) *)
runml(TAIL(APPEND(CONS(CONST 1,NIL),CONS (CONST 2, CONS(CONST 3,NIL))))) = List [Int 2; Int 3];;

(* 1::3 *)
(*runml(CONS(CONST 1,CONST 3));;*)

(* let x = 10 in if x<true then 1 else 2 *)
(*runml(LET("x",CONST 10, IF(LESS(VAR "x",TRUE),CONST 1,CONST 2)));;*)

(* 1;if 5<6 then 4/2 else 3 *)
runml(SEQ(CONST 1,IF (LESS (CONST 5,CONST 6),DIV (CONST 4, CONST 2),CONST 3))) = Int 2;;

(* let x = 1 in 1;x *)
(*runml(SEQ(LET("x",CONST 1,CONST 1),VAR "x"));;*)

(* (proc (x) (x::[])) 1 *)
runml(CALL(PROC ("x",CONS (VAR "x",NIL)),CONST 1)) = List [Int 1];;

(* let f = proc (x) (x+x) in (f 5) *)
runml(LET("f",PROC("x",ADD(VAR "x",VAR "x")),CALL (VAR "f",CONST 5))) = Int 10;;

(* 
  let x = 5 in 
    let x = x+x in
      x 
*)
runml(LET("x",CONST 5,LET("x",ADD(VAR "x",VAR "x"),VAR "x"))) = Int 10;;

(*
  let rec factorial x = 
    if (x<1) then 1 else factorial (x-1) in
      factorial 5
*)
runml(LETREC("factorial","x",IF(LESS(VAR "x",CONST 1),CONST 1,MUL(VAR "x",CALL (VAR "factorial",SUB(VAR "x",CONST 1)))),CALL (VAR "factorial",CONST 5))) = Int 120;;

(*
  let x = 2 in
    let f = proc (y) (x+y) in
      let x = 5 in
        (f 3)
*)
runml(LET("x",CONST 2,LET ("f",PROC("y",ADD(VAR "y",VAR "x")),LET("x",CONST 5,CALL (VAR "f",CONST 3))))) = Int 5;;

(*
  let f = proc (x) (proc (y) (proc (z) (x+y+z))) in
    (f 1 2 3)
*)
runml(LET("f",PROC("x",PROC("y",PROC("z",ADD(VAR "x",ADD(VAR "y",VAR "z"))))),CALL(CALL(CALL(VAR "f",CONST 1),CONST 2),CONST 3))) = Int 6;;

(*
  let rec drop f = proc (lst) (
    if lst=[] then [] else 
      if f (head(lst)) then drop f (tail(lst)) else lst
  ) in drop (proc (x) (5<x)) [1;3;7]
*)
runml(LETREC("drop","f",PROC("lst",IF(ISNIL(VAR "lst"),NIL,IF(CALL(VAR "f",HEAD(VAR "lst")),CALL(CALL(VAR "drop",VAR "f"),TAIL(VAR "lst")),VAR "lst"))),CALL(CALL(VAR "drop",PROC("x",LESS(CONST 5,VAR "x"))),CONS(CONST 1,CONS(CONST 3,CONS (CONST 7,NIL)))))) = List [Int 1;Int 3;Int 7];;

(*
  let rec concat lst = 
    if lst=[] then [] else head(lst)@(concat tail(lst))
  in concat [[1;2];[3;4;5]]
*)
runml(LETREC("concat","lst",IF(ISNIL(VAR "lst"),NIL,APPEND(HEAD(VAR "lst"),CALL(VAR "concat",TAIL(VAR "lst")))),CALL(VAR "concat",CONS(CONS(CONST 1,CONS(CONST 2,NIL)),CONS(CONS(CONST 3,CONS (CONST 4,CONS (CONST 5,NIL))),NIL))))) = List [Int 1;Int 2;Int 3;Int 4;Int 5];;

(*
  let x = 2 in
    let rec f x = g x
    and g y = x+2 
   in f 5
*)
runml(LET("x",CONST 2,LETMREC(("f","x",CALL (VAR "g",VAR "x")),("g","y",ADD(VAR "x",CONST 2)),CALL (VAR "f",CONST 5)))) = Int 4;;

(*
  let rec f lst =
    if lst=[] then [] else (f (tail(lst)))@(g (lst))
  and g lst = 
    if lst=[] then [] else head(lst)::(f (tail(lst)))
  in (f [1;3;5])
*)
runml(LETMREC(("f","lst",IF(ISNIL(VAR "lst"),NIL,APPEND(CALL(VAR "f",TAIL(VAR "lst")),CALL(VAR "g",VAR "lst")))),("g","lst",IF(ISNIL(VAR "lst"),NIL,CONS(HEAD(VAR "lst"),CALL(VAR "f",TAIL(VAR "lst"))))),CALL(VAR "f",CONS(CONST 1,CONS(CONST 3,CONS(CONST 5,NIL)))))) = List [Int 5;Int 3;Int 5;Int 1;Int 5;Int 3;Int 5];;

(*
  let x = 2 in
    let rec f y = if(y=0) then 0 else x+(f (y-1)) in 
  let x = 5 in
  (f x) 
*)
runml(LET("x",CONST 2,LETREC("f","y",IF(EQUAL(VAR "y",CONST 0),CONST 0,ADD(VAR "x",CALL (VAR "f", SUB(VAR "y",CONST 1)))),LET("x",CONST 5,CALL (VAR "f",VAR "x"))))) = Int 10;;

(*
  let rec iter n = proc (f) (
    if n=0 then proc (x) x 
    else proc (x) (iter (n-1) (f x))
  ) in (iter 3 (proc (x) (x+2)) 3)
*)
runml(LETREC("iter","n",PROC("f",IF(EQUAL(VAR "n",CONST 0),PROC("x",VAR "x"),PROC("x",CALL(CALL(CALL(VAR "iter",SUB(VAR "n",CONST 1)),VAR "f"),CALL (VAR "f",VAR "x"))))),CALL(CALL(CALL(VAR "iter",CONST 3),PROC ("x",ADD(VAR "x",CONST 2))),CONST 3))) = Int 9;;

(*
  let rec f n = if (0<n) then (f (n-1)+ n*(g n)) else 0
  and g n = if (0<n) then (1+f(n-1)) else 1
  in (f 5)
*)
runml(LETMREC(("f","n",IF(LESS(CONST 0,VAR "n"),ADD(CALL(VAR "f",SUB(VAR "n",CONST 1)),MUL(VAR "n",CALL(VAR "g",VAR "n"))),CONST 0)),("g","n",IF(LESS(CONST 0,VAR "n"),ADD(CONST 1,CALL(VAR "f",SUB(VAR "n",CONST 1))),CONST 1)),CALL(VAR "f",CONST 5))) = Int 719;;

(*
  let rec g x = f 1 
  and f y = x+2 in
  (g 2)
*)
(*runml(LETMREC(("g","x",CALL(VAR "f",CONST 1)),("f","y",ADD(VAR "x",CONST 2)),CALL(VAR "g",CONST 2)));;*)

(*
  let rec sub x = if x=0 then 0 else x+(sub (x-1))
  and f x = 
    let x = x/2 in
    (sub x)
  in (f 10)
*)
runml(LETMREC(("sub","x",IF(EQUAL(VAR "x",CONST 0),CONST 0,ADD(VAR "x",CALL(VAR "sub",SUB(VAR "x",CONST 1))))),("f","x",LET("x",DIV(VAR "x",CONST 2),CALL(VAR "sub",VAR "x"))),CALL(VAR "f", CONST 10))) = Int 15;;