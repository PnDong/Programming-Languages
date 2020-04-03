type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp                 (* sequence *)
  | IF of exp * exp * exp            (* if-then-else *)
  | WHILE of exp * exp               (* while loop *)
  | LETV of id * exp * exp           (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list           (* call by value *)
  | CALLR of id * id list            (* call by referenece *)
  | RECORD of (id * exp) list        (* record construction *)
  | FIELD of exp * id                (* access record field *)
  | ASSIGN of id * exp               (* assgin to variable *)
  | ASSIGNF of exp * id * exp        (* assign to record field *)
  | WRITE of exp
and id = string

type loc = int
type value =
| Num of int
| Bool of bool
| Unit
| Record of record 
and record = (id * loc) list
type memory = (loc * value) list
type env = binding list
and binding = LocBind of id * loc | ProcBind of id * proc
and proc = id list * exp * env

(************************************)
(*      List utility functions      *)
(************************************)
let rec list_length : 'a list -> int
= fun lst ->
  match lst with
  | [] -> 0
  | hd::tl -> 1 + list_length tl

let rec list_exists : ('a -> bool) -> 'a list -> bool
= fun pred lst ->
  match lst with 
  | [] -> false 
  | hd::tl -> if (pred hd) then true else list_exists pred tl

let rec list_fold2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
= fun func acc lst1 lst2 ->
  match (lst1, lst2) with
  | ([], []) -> acc
  | (hd1::tl1, hd2::tl2) -> list_fold2 func (func acc hd1 hd2) tl1 tl2
  | _ -> raise (Failure "list_fold2 : two lists have different length")

let rec list_fold : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
= fun func acc lst ->
  match lst with
  | [] -> acc
  | hd::tl -> list_fold func (func acc hd) tl 

(********************************)
(*     Handling environment     *)
(********************************)
let rec lookup_loc_env : id -> env -> loc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind (id, l) -> if (x = id) then l else lookup_loc_env x tl
    | ProcBind _ -> lookup_loc_env x tl
    end

let rec lookup_proc_env : id -> env -> proc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind _ -> lookup_proc_env x tl
    | ProcBind (id, binding) -> if (x = id) then binding else lookup_proc_env x tl
    end

let extend_env : binding -> env -> env
= fun e env -> e::env

let empty_env = []

(***************************)
(*     Handling memory     *)
(***************************)
let rec lookup_mem : loc -> memory -> value
= fun l mem ->
  match mem with
  | [] -> raise (Failure ("location "^(string_of_int l)^" is not included in memory"))
  | (loc, v)::tl -> if (l = loc) then v else lookup_mem l tl

let extend_mem : (loc * value) -> memory -> memory
= fun (l, v) mem -> (l, v)::mem

let empty_mem = []

let size_of_mem mem = 
  let add_if_new x l = if list_exists (fun y -> x = y) l then l else x::l in
  let dom = list_fold (fun dom loc -> add_if_new loc dom) [] mem  in
    list_length dom

(***************************)
(*     Handling record     *)
(***************************)
let rec lookup_record : id -> record -> loc
= fun id record -> 
  match record with
  | [] -> raise(Failure ("field "^ id ^" is not included in record"))
  | (x, l)::tl -> if (id = x) then l else lookup_record id tl


let extend_record : (id * loc) -> record -> record
= fun (x, l) record -> (x, l)::record

let empty_record = []

(******************)
(* Pretty printer *)
(******************)
let rec value2str : value -> string
= fun v ->
  match v with
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "unit"
  | Record r -> "{" ^ record2str r ^ "}" 

and record2str : record -> string
= fun record ->
  match record with
  | [] -> ""
  | [(x, l)] -> x ^ "->" ^ string_of_int l
  | (x, l)::tl-> x ^ "->" ^ string_of_int l ^ ", " ^ record2str tl

let mem2str : memory -> string
= fun mem -> 
  let rec aux mem =
    match mem with
    | [] -> ""
    | [(l, v)] -> string_of_int l ^ "->" ^ value2str v
    | (l, v)::tl -> string_of_int l ^ "->" ^ value2str v ^ ", " ^ aux tl
  in
  "[" ^ aux mem ^ "]"

let rec env2str : env -> string
= fun env -> 
  let rec aux env =
    match env with
    | [] -> ""
    | [binding] -> binding2str binding
    | binding::tl -> binding2str binding ^ ", " ^ aux tl
  in
  "[" ^ aux env ^ "]"

and binding2str : binding -> string
= fun binding ->
  match binding with
  | LocBind (x, l) -> x ^ "->" ^ string_of_int l
  | ProcBind (x, proc) -> x ^ "->" ^ "(" ^ proc2str proc ^ ")"

and proc2str : proc -> string
= fun (xs, e, env) ->  
  let rec args2str xs =
    match xs with
    | [] -> ""
    | [x] -> x
    | x::tl -> x ^ ", " ^ args2str tl
  in
  "(" ^ args2str xs ^ ")" ^ ", E" ^ ", " ^ env2str env

(***************************)
let counter = ref 0
let new_location () = counter:=!counter+1;!counter

exception NotImplemented
exception UndefinedSemantics

let rec eval_aop : env -> memory -> exp -> exp -> (int -> int -> int) -> (value * memory)
= fun env mem e1 e2 op ->
  let (v1, mem1) = eval env mem e1 in
  let (v2, mem2) = eval env mem1 e2 in
  match (v1, v2) with
  | (Num n1, Num n2) -> (Num (op n1 n2), mem2)
  | _ -> raise (Failure "arithmetic operation type error")

and eval : env -> memory -> exp -> (value * memory)
=fun env mem e -> 
  let mem = gc env mem in
  match e with
  | WRITE e -> 
    let (v1, mem1) = eval env mem e in
    let _ = print_endline (value2str v1) in
    (v1, mem1)
  | TRUE -> (Bool true, mem)
  | FALSE -> (Bool false, mem)
  | NUM n -> (Num n, mem)
  | UNIT -> (Unit, mem)
  | VAR x -> (lookup_mem (lookup_loc_env x env) mem, mem)
  | ADD (e1, e2) -> eval_aop env mem e1 e2 (+)
  | SUB (e1, e2) -> eval_aop env mem e1 e2 (-)
  | MUL (e1, e2) -> eval_aop env mem e1 e2 (fun x y -> x * y)
  | DIV (e1, e2) -> eval_aop env mem e1 e2 (/)
  | EQUAL (e1, e2) ->
    let (v1, mem1) = eval env mem e1 in
    let (v2, mem2) = eval env mem1 e2 in (
    match v1, v2 with
    | Num n1, Num n2 -> if n1 = n2 then (Bool true, mem2) else (Bool false, mem2)
    | Bool b1, Bool b2 -> if b1 = b2 then (Bool true, mem2) else (Bool false, mem2)
    | Unit, Unit -> (Bool true, mem2)
    | _ -> (Bool false, mem2) )
  | LESS (e1, e2) ->
    let (v1, mem1) = eval env mem e1 in
    let (v2, mem2) = eval env mem1 e2 in (
    match v1, v2 with
    | Num n1, Num n2 -> if n1 < n2 then (Bool true, mem2) else (Bool false, mem2)
    | _ -> raise UndefinedSemantics )
  | NOT e ->
    let (v1, mem1) = eval env mem e in (
    match v1 with
    | Bool b -> (Bool (not b), mem1)
    | _ -> raise UndefinedSemantics )
  | SEQ (e1, e2) ->
    let (v1, mem1) = eval env mem e1 in
    let (v2, mem2) = eval env mem1 e2 in (v2, mem2)
  | IF (e, e1, e2) ->
    let (v1, mem1) = eval env mem e in (
    match v1 with
    | Bool true -> eval env mem1 e1
    | Bool false -> eval env mem1 e2
    | _ -> raise UndefinedSemantics )
  | WHILE (e1, e2) ->
    let (v1, mem1) = eval env mem e1 in (
    match v1 with
    | Bool true -> let (v2, mem2) = eval env mem1 e2 in eval env mem2 (WHILE (e1, e2))
    | Bool false -> (Unit, mem1)
    | _ -> raise UndefinedSemantics )
  | LETV (x, e1, e2) ->
    let (v1, mem1) = eval env mem e1 in
    let new_loc = new_location () in
    eval (extend_env (LocBind (x, new_loc)) env) (extend_mem (new_loc, v1) mem1) e2
  | LETF (f, x_lst, e1, e2) ->
    eval (extend_env (ProcBind (f, (x_lst, e1, env))) env) mem e2
  | CALLV (f, e_lst) ->
    let (x_lst, e1, env1) = lookup_proc_env f env in
    let (v_lst, last_m) = list_fold (fun (acc_v_lst, acc_mem) exp -> let (v, m) = (eval env acc_mem exp) in (acc_v_lst @ [v], m)) ([], mem) e_lst in
    let (new_env, new_mem) =
      list_fold2
        (fun (env, mem) id v -> let new_loc = new_location () in (extend_env (LocBind (id, new_loc)) env, extend_mem (new_loc, v) mem))
        (env1, last_m)
        x_lst
        v_lst
    in eval (extend_env (ProcBind (f, (x_lst, e1, env1))) new_env) new_mem e1
  | CALLR (f, y_lst) ->
    let (x_lst, e, env1) = (lookup_proc_env f env) in
    let new_env = list_fold2 (fun envr id id2 -> extend_env (LocBind (id2, lookup_loc_env id env)) envr) env1 y_lst x_lst
    in eval new_env mem e
  | RECORD (x_e_lst) ->
    if (list_length x_e_lst) = 0 then (Unit, mem) else
    let (v_lst, last_m) = list_fold (fun (acc_v_lst, acc_mem) (x, e) -> let (v, m) = (eval env acc_mem e) in (acc_v_lst @ [v], m)) ([], mem) x_e_lst in
    let (record, final_m) =
      list_fold2
        (fun (acc_record, acc_mem) (x, e) v -> let new_loc = new_location () in (extend_record (x, new_loc) acc_record, extend_mem (new_loc, v) acc_mem))
        (empty_record, last_m)
        x_e_lst
        v_lst
    in (Record record, final_m)
  | FIELD (e, x) -> (
    match (eval env mem e) with
    | (Record record, mem1) -> (lookup_mem (lookup_record x record) mem1, mem1)
    | _ -> raise UndefinedSemantics )
  | ASSIGN (x, e) ->
    let (v1, mem1) = eval env mem e
    in (v1, extend_mem (lookup_loc_env x env, v1) mem1)
  | ASSIGNF (e1, x, e2) -> (
      match (eval env mem e1) with
      | (Record record, mem1) ->
        let (v, mem2) = eval env mem1 e2
        in (v, extend_mem (lookup_record x record, v) mem2)
      | _ -> raise UndefinedSemantics )

and gc : env -> memory -> memory
= fun env mem ->
  let mem =
    (* Removing old memory *)
    let rec rebuild_mem mem1 ex =
      match mem1 with
      | [] -> []
      | (l, v)::tl -> if list_exists (fun (l1, v1) -> l1 = l) ex then rebuild_mem tl ex else (l, v)::(rebuild_mem tl ((l, v)::ex))
    in rebuild_mem mem []
  in
  
  (* Get fix *)
  let cons_if_not_exist v lst = if list_exists (fun x -> x = v) lst then lst else v::lst in
  let append_not_exist lst1 lst2 = list_fold (fun acc v -> cons_if_not_exist v acc) lst2 lst1 in
  let env_direct_reachable envr =
    list_fold (fun (acc_loc, acc_proc) b ->
      match b with
      | LocBind (_, l) -> (cons_if_not_exist l acc_loc, acc_proc)
      | ProcBind (_, p) -> (acc_loc, cons_if_not_exist p acc_proc)) ([], []) envr in
  let one_step_reachable (loc_lst, proc_lst) =
    let loc_one_step mem l =
      match (lookup_mem l mem) with
      | Record r -> list_fold (fun acc (_, l) -> cons_if_not_exist l acc) [] r
      | _ -> []
    in
    let proc_one_step (x_lst, e, env1) = env_direct_reachable env1  in
    let new_loc_lst = list_fold (fun acc_loc l -> append_not_exist (loc_one_step mem l) acc_loc) loc_lst loc_lst  in
    let new_loc_proc_lst =
      let (new_loc_lst2, new_proc_lst) =
        list_fold (fun (acc_loc, acc_proc) p -> let (osl, osp) = proc_one_step p in (append_not_exist osl acc_loc, append_not_exist osp acc_proc)) (loc_lst, proc_lst) proc_lst
      in (append_not_exist new_loc_lst2 new_loc_lst, new_proc_lst)
    in new_loc_proc_lst
  in
  let rec reachable_fix set = if (one_step_reachable set) = set then set else reachable_fix (one_step_reachable set)  in
  let (reachable_loc_lst, reachable_proc_lst) = reachable_fix (env_direct_reachable env)  in

  (* Remove unreachable locations *)
  print_endline (mem2str (list_fold (fun acc (l, v) -> if list_exists (fun x -> x = l) reachable_loc_lst then acc@[(l,v)] else ((print_endline ("("^(string_of_int l)^"->"^(value2str v)^") deleted"));acc)) [] mem));
  list_fold (fun acc (l, v) -> if list_exists (fun x -> x = l) reachable_loc_lst then acc@[(l,v)] else acc) [] mem

let runb : exp -> value 
= fun exp ->
  let (v, m) = eval empty_env empty_mem exp in
  let _ = print_endline ("memory size: " ^ string_of_int (size_of_mem m)) in
    v;;

runb (LETV ("ret", NUM 1,
LETV ("n", NUM 5,
SEQ (
WHILE (LESS (NUM 0, VAR "n"),
SEQ (
ASSIGN ("ret", MUL (VAR "ret", VAR "n")),
ASSIGN ("n", SUB (VAR "n", NUM 1))
)
),
VAR "ret"))));;

runb(LETF ("f", ["x1"; "x2"],
SEQ (
ASSIGN ("x1", NUM 3),
ASSIGN ("x2", NUM 3)
),
LETV("x1", NUM 1,
LETV("x2", NUM 1,
SEQ(
CALLR ("f", ["x1"; "x2"]),
ADD(VAR "x1", VAR "x2")))))
);;

runb (LETV ("f", RECORD ([("x", NUM 10); ("y", NUM 13)]),
LETF ("swap", ["a"; "b"],
LETV ("temp", VAR "a",
SEQ (
ASSIGN ("a", VAR "b"),
ASSIGN ("b", VAR "temp"))),
SEQ (
CALLV("swap", [FIELD (VAR "f", "x"); FIELD (VAR "f", "y")]),
FIELD (VAR "f", "x")
)
)
));;

runb (LETV ("x", NUM 3, LETV ("y", NUM 4, ADD (LETV ("x", ADD(VAR "y", NUM 5), MUL (VAR "x", VAR "y")), VAR "x"))));;