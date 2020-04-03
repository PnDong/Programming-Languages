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

exception TypeError

type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string
type typ_eqn = (typ * typ) list

let rec string_of_type ty = 
  match ty with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1,t2) -> "(" ^ string_of_type t1 ^ " -> " ^ string_of_type t2 ^ ")"
  | TyVar x -> x

let print_typ_eqns eqns = 
  List.iter (fun (ty1,ty2) -> print_string (string_of_type ty1 ^ " = " ^ string_of_type ty2 ^ "\n")) eqns;
  print_endline ""

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  =fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x -> 
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the subsutition and propagate the information *)
  let extend tv ty subst = 
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)

  let print : t -> unit
  =fun subst -> 
      List.iter (fun (x,ty) -> print_endline (x ^ " |-> " ^ string_of_type ty)) subst
end

let tyvar_num = ref 0

(* generate a fresh type variable *)
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn 
=fun tenv e ty ->
  match e with 
  | CONST n -> [(ty, TyInt)]
  | VAR x -> [(ty, TEnv.find tenv x)]
  | ADD (e1, e2) -> (ty, TyInt)::(gen_equations tenv e1 TyInt)@(gen_equations tenv e2 TyInt)
  | SUB (e1, e2) -> (ty, TyInt)::(gen_equations tenv e1 TyInt)@(gen_equations tenv e2 TyInt)
  | MUL (e1, e2) -> (ty, TyInt)::(gen_equations tenv e1 TyInt)@(gen_equations tenv e2 TyInt)
  | DIV (e1, e2) -> (ty, TyInt)::(gen_equations tenv e1 TyInt)@(gen_equations tenv e2 TyInt)
  | ISZERO e -> (ty, TyBool)::(gen_equations tenv e TyInt)
  | READ -> [(ty, fresh_tyvar ())]
  | IF (e1, e2, e3) -> (gen_equations tenv e1 TyBool)@(gen_equations tenv e2 ty)@(gen_equations tenv e3 ty)
  | LET (x, e1, e2) ->
    let ty1 = fresh_tyvar () in
      (gen_equations tenv e1 ty1)@(gen_equations (TEnv.extend (x, ty1) tenv) e2 ty)
  | LETREC (f, x, e1, e2) ->
    let ty1 = fresh_tyvar () in
    let ty2 = fresh_tyvar () in
      (gen_equations (TEnv.extend (f, TyFun (ty1, ty2)) (TEnv.extend (x, ty1) tenv)) e1 ty2)@(gen_equations (TEnv.extend (f,  TyFun (ty1, ty2)) tenv) e2 ty)
  | PROC (x, e) ->
    let ty1 = fresh_tyvar () in
    let ty2 = fresh_tyvar () in
    (ty, TyFun (ty1, ty2))::(gen_equations (TEnv.extend (x, ty1) tenv) e ty2)
  | CALL (e1, e2) ->
    let ty1 = fresh_tyvar () in
      (gen_equations tenv e1 (TyFun (ty1, ty)))@(gen_equations tenv e2 ty1)

let solve : typ_eqn -> Subst.t
=fun eqns ->
  let rec occurs_in = fun a ty ->
    match ty with
    | TyVar b -> if a = b then true else false
    | TyFun (ty1, ty2) -> (occurs_in a ty1) || (occurs_in a ty2)
    | _ -> false
  in
  let rec unify = fun typ1 typ2 subst ->
    match typ1, typ2 with
    | (TyInt, TyInt) -> subst
    | (TyBool, TyBool) -> subst
    | (TyVar a, ty) -> (
      match ty with
      | TyInt -> Subst.extend a ty subst
      | TyBool -> Subst.extend a ty subst
      | TyVar b -> if a = b then subst else Subst.extend a (TyVar b) subst
      | TyFun (ty1, ty2) -> if (occurs_in a ty) then raise TypeError else Subst.extend a ty subst
      )
    | (ty, TyVar a) -> unify (TyVar a) ty subst
    | (TyFun (t1, t2), TyFun (t1', t2')) ->
      let subst' = unify t1 t1' subst in
      let subst'' = unify (Subst.apply t2 subst') (Subst.apply t2' subst') subst' in subst''
    | (_, _) -> raise TypeError
  in
  let rec unifyall = fun curr_eqn curr_subst ->
    match curr_eqn with
    | [] -> curr_subst
    | (ty1, ty2)::u ->
      let s = unify (Subst.apply ty1 curr_subst) (Subst.apply ty2 curr_subst) curr_subst
      in unifyall u s
  in unifyall eqns Subst.empty

let typeof : exp -> typ 
=fun exp ->
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let _ = print_endline "= Equations = ";
          print_typ_eqns eqns in
  try 
    let subst = solve eqns in
    let ty = Subst.apply new_tv subst in
      print_endline "= Substitution = ";
      Subst.print subst;
      print_endline "";
      print_endline ("Type of the given program: " ^ string_of_type ty);
      print_endline "";
      ty
  with TypeError -> (print_endline "The program does not have type. Rejected."); exit (1);;
