open Fbast

exception TypeMismatch;; 
exception NotClosed;;   

(* check_closed, a function which determines whether or not an expression is closed (no free variables) *)
let rec check_closed e env =
  match e with
  | Var(var) -> List.mem var env          (* Don't want to raise NotClose if Var(var) just yet *)
  | Int(_) | Bool(_) -> true              (* Integers and Booleans are considered closed *)
  | Not(e1) -> check_closed e1 env

  | Function(arg, e1) -> check_closed e1 (arg::env)      (* arg is added to the environment, helps with a lot of the failed function cases *)

  | And(e1, e2) | Or(e1, e2) | Plus(e1, e2) | Minus(e1, e2) | Equal(e1, e2) | Appl(e1, e2) -> 
      check_closed e1 env && check_closed e2 env

  | If(e1, e2, e3) -> check_closed e1 env && check_closed e2 env && check_closed e3 env

  | Let(var, e1, e2) ->
      let bound_closed = check_closed e1 env in               (* Checking if the bound expression is closed *)
        let body_closed = check_closed e2 (var::env) in       (* Checking if the body is closed in the environment where the variable is bound *)
          bound_closed && body_closed

  | LetRec(_, _, _, _) -> raise NotClosed

let rec eval e =  (* Can pattern match most operational semantics rules in one recursive call *)
  match e with 

  (* Value Rule *)
  | Var(name) -> raise NotClosed (* A variable w/o a bound value within the current scope signifies a free variable *)
  | Int(num) -> Int(num)
  | Bool(b) -> Bool(b)

  (* Evaluate e1 (and e2, e3, .. etc) before operation *)
  (* Hence, we pattern match and recursively call *)

  | Not(e) -> (
    match eval e with  
    | Bool(b) -> Bool(not b)                    (* not must be wrapped within node *)
    | _ -> raise TypeMismatch                   (* cannot negate an int *)
  )                  

  | And(e1, e2) -> (
    match (eval e1, eval e2) with
    | (Bool(b1), Bool(b2)) -> Bool(b1 && b2)
    | _ -> raise TypeMismatch
  )

  | Or(e1, e2) -> (
    match (eval e1, eval e2) with
    | (Bool(b1), Bool(b2)) -> Bool(b1 || b2)
    | _ -> raise TypeMismatch
  )

  | Plus(e1, e2) -> (
    match (eval e1, eval e2) with
    | (Int(i1), Int(i2)) -> Int(i1 + i2)
    | _ -> raise TypeMismatch
  )                    

  | Minus(e1, e2) -> (
    match (eval e1, eval e2) with
    | (Int(i1), Int(i2)) -> Int(i1 - i2)
    | _ -> raise TypeMismatch
  )

  | Equal(e1, e2) -> (
    match (eval e1, eval e2) with
    | (Int(i1), Int(i2)) -> Bool(i1 = i2)
    (* | (Bool(b1), Bool(b2)) -> Bool(b1 = b2) --- FAILURE --- True = True Failure("Expected exception.") *)
    | _ -> raise TypeMismatch
  )

  | If(e1, e2, e3) -> (
    match eval e1 with          (* evaluate corresponding body *)
    | Bool(true) -> eval e2
    | Bool(false) -> eval e3
    | _ -> raise TypeMismatch
  )

  | Function(arg, body) -> Function(arg, body)
  (* variables found in function body has to be found in function arg *)
 
  | Appl(e1, e2) -> (
    (* before applying, check close *)
    if not(check_closed e1 [] && check_closed e2 []) then raise NotClosed else
      match eval e1 with
      | Function(arg, body) ->
          let subst_body = subst body arg (eval e2) in
          eval subst_body  (* evaluate the substituted body *)
      | _ -> raise TypeMismatch
    )

  (* let expression shouldn't contain unsubstituted variables *)
  | Let(var, e1, e2) ->
    let bound_value = eval e1 in
      eval (subst e2 var bound_value)

  | LetRec(f, arg, fbody, e) -> raise TypeMismatch

(* function for substiution, based on the book *)
and subst expr id subst_expr =
  match expr with
  | Var(name) when name = id -> subst_expr (* if names match, replace variable with substitution *)
  | Var(_) -> expr
  | Int(_) -> expr
  | Bool(_) -> expr

  | Plus(e1, e2) -> Plus(subst e1 id subst_expr, subst e2 id subst_expr)
  | Minus(e1, e2) -> Minus(subst e1 id subst_expr, subst e2 id subst_expr)
  | Equal(e1, e2) -> Equal(subst e1 id subst_expr, subst e2 id subst_expr)
  | And(e1, e2) -> And(subst e1 id subst_expr, subst e2 id subst_expr)
  | Or(e1, e2) -> Or(subst e1 id subst_expr, subst e2 id subst_expr)
  | Not(e) -> Not(subst e id subst_expr)
  | If(e1, e2, e3) -> If(subst e1 id subst_expr, subst e2 id subst_expr, subst e3 id subst_expr)

  | Function(arg, body) -> 
      if arg = id then 
        Function(arg, body) (* leave as it is *)
      else
        Function(arg, subst body id subst_expr)

  | Appl(e1, e2) -> Appl(subst e1 id subst_expr, subst e2 id subst_expr)
  
  | Let(let_id, let_expr1, let_expr2) -> 
      if let_id = id then
        Let(let_id, subst let_expr1 id subst_expr, let_expr2)
      else
        Let(let_id, subst let_expr1 id subst_expr, subst let_expr2 id subst_expr)

  | LetRec(f, arg, fbody, e) -> raise TypeMismatch

