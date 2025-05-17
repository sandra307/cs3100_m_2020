let name = ""
let rollno = ""

type constant = Constant of string
type variable = Variable of string
type func = Function of string * term list
and term = C of constant | V of variable | F of func

type predicate = Predicate of string * term list

type head = predicate
type body = predicate list

type clause = Fact of head | Rule of head * body

type goal = predicate list

type program = clause list

let rec string_of_f_list f tl =
  let _, s = List.fold_left (fun (first, s) t -> 
    let prefix = if first then "" else s ^ ", " in
    false, prefix ^ (f t)) (true,"") tl
  in 
  s

let rec string_of_term t =
  match t with
  | C (Constant c) -> c
  | V (Variable v) -> v
  | F (Function (f,tl)) -> 
      f ^ "(" ^ (string_of_f_list string_of_term tl) ^ ")"

let string_of_predicate (Predicate (p,tl)) =
  p ^ "(" ^ (string_of_f_list string_of_term tl) ^")"
  
let string_of_predicate_list pl =
  string_of_f_list string_of_predicate pl
  
let string_of_goal g =
  "?- " ^ (string_of_predicate_list g)

let string_of_clause c =
  match c with
  | Fact f -> string_of_predicate f ^ "."
  | Rule (h,b) -> string_of_predicate h ^ " :- " ^ (string_of_predicate_list b) ^ "."

let string_of_program p =
  List.fold_left (fun acc c -> acc ^ (string_of_clause c) ^ "\n") "" p

let var v = Variable v
let var_t v = V (var v)
let const c = Constant c
let const_t c = C (Constant c)
let func f l = Function (f,l)
let func_t f l = F (func f l)
let pred p l = Predicate (p,l)
let fact f = Fact f
let rule h b = Rule (h,b)

let rec occurs_check v t = 
  match t with 
  C _->false|
  V x->v=x|
  F (Function (_, y)) ->        
      List.exists (occurs_check v) y

(* 5 points *)
assert (occurs_check (var "X") (var_t "X"));
assert (not (occurs_check (var "X") (var_t "Y")));
assert (occurs_check (var "X") (func_t "f" [var_t "X"]))

module VarSet = Set.Make(struct type t = variable let compare =Stdlib.compare end)
(* API Docs for Set : https://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html *)


let rec variables_of_term t =
  match t with
  | C _ -> VarSet.empty                      
  | V v -> VarSet.singleton v               
  | F(Function (_, y)) ->                
      List.fold_left
        (fun acc k-> VarSet.union acc (variables_of_term k))
        VarSet.empty
        y

  
let rec variables_of_predicate (Predicate (_, l)) =
List.fold_left(fun acc t->VarSet.union acc(variables_of_term t)) VarSet.empty
l
  
  
let variables_of_clause c =
  match c with
  | Fact p -> variables_of_predicate p
  | Rule (h, b) ->
      let h1 = variables_of_predicate h in
      let b1 = List.fold_left
        (fun acc k -> VarSet.union acc (variables_of_predicate k))
        VarSet.empty
        b
      in
      VarSet.union h1 b1
  

(* 5 points *)
assert (variables_of_term (func_t "f" [var_t "X"; var_t "Y"; const_t "a"]) = 
        VarSet.of_list [var "X"; var "Y"]);
assert (variables_of_predicate (pred "p" [var_t "X"; var_t "Y"; const_t "a"]) = 
        VarSet.of_list [var "X"; var "Y"]);
assert (variables_of_clause (fact @@ pred "p" [var_t "X"; var_t "Y"; const_t "a"]) = 
        VarSet.of_list [var "X"; var "Y"]);
assert (variables_of_clause (rule (pred "p" [var_t "X"; var_t "Y"; const_t "a"]) [pred "q" [const_t "a"; const_t "b"; const_t "a"]])= 
        VarSet.of_list [var "X"; var "Y"])

module Substitution = Map.Make(struct type t = variable let compare = Stdlib.compare end)
(* See API docs for OCaml Map: https://caml.inria.fr/pub/docs/manual-ocaml/libref/Map.S.html *)
let string_of_substitution s =
  "{" ^ (Substitution.fold (fun (Variable v) t s -> s ^ "; " ^ v ^ " -> " ^ (string_of_term t)) s "") ^ "}"


let rec substitute_in_term s t =
  match t with
   C _ -> t|
   V v->(try Substitution.find v s with Not_found->t)|
   F(Function(n,a))->let na=List.map(substitute_in_term s) a in F(Function(n,na))
  
 
let rec substitute_in_predicate s (Predicate (p,l)) =
Predicate(p,List.map(substitute_in_term s)l)
  
  
let substitute_in_clause s c =
match c with 
    Fact p->Fact(substitute_in_predicate s p)|
    Rule (h,b)->let h1=substitute_in_predicate s h in
    let b1=List.map(substitute_in_predicate s )b in
    Rule (h1,b1)




  


(* 10 points *)
let s = 
  let open Substitution in 
  add (var "Y") (const_t "0") (add (var "X") (var_t "Y") empty)
in
assert (substitute_in_term s (func_t "f" [var_t "X"; var_t "Y"; const_t "a"]) = 
        func_t "f" [var_t "Y"; const_t "0"; const_t "a"]);
assert (substitute_in_predicate s (pred "p" [var_t "X"; var_t "Y"; const_t "a"]) = 
        pred "p" [var_t "Y"; const_t "0"; const_t "a"]);
assert (substitute_in_clause s (fact @@ pred "p" [var_t "X"; var_t "Y"; const_t "a"]) = 
        (fact @@ pred "p" [var_t "Y"; const_t "0"; const_t "a"]));
assert (substitute_in_clause s (rule (pred "p" [var_t "X"; var_t "Y"; const_t "a"]) [pred "q" [const_t "a"; const_t "b"; const_t "a"]]) = 
        (rule (pred "p" [var_t "Y"; const_t "0"; const_t "a"]) [pred "q" [const_t "a"; const_t "b"; const_t "a"]]))

let counter = ref 0
let fresh () = 
  let c = !counter in
  counter := !counter + 1;
  V (Variable ("_G" ^ string_of_int c))

let freshen c =
  let vars = variables_of_clause c in
  let s = VarSet.fold (fun v s -> Substitution.add v (fresh()) s) vars Substitution.empty in
  substitute_in_clause s c

let c = (rule (pred "p" [var_t "X"; var_t "Y"; const_t "a"]) [pred "q" [var_t "X"; const_t "b"; const_t "a"]])
let _ = string_of_clause c
let _ = string_of_clause (freshen c)

let rec apply_subst s t =
   match t with
 C _->t|
 V v->(match List.assoc_opt v s with
 Some t'->apply_subst s t'|
 None->t
 )|
F(Function(n,a))->F(Function(n,List.map(apply_subst s )a))

exception Not_unifiable

let mgu t1 t2 = 
let rec unify s t1 t2=
let t1=substitute_in_term s t1 in
let t2=substitute_in_term s t2 in
match t1,t2 with
C c1,C c2 when c1=c2->s|
V v1,V v2 when v1=v2->s|
V v,t|t,V v->
if t=V v then s 
else if occurs_check v t then raise Not_unifiable
else 
let sub'=Substitution.singleton v t in
Substitution.fold(fun key value acc->
Substitution.add key(substitute_in_term sub' value)acc )s sub' |>Substitution.add v t
|F (Function(f1,a1)),F (Function(f2,a2))->if f1<>f2||List.length a1<>List.length a2 then raise Not_unifiable else
List.fold_left2 unify s a1 a2 |
_,_->raise Not_unifiable in
unify Substitution.empty t1 t2 
let mgu_predicate (Predicate (p1,l1)) (Predicate (p2,l2)) =
if p1<>p2||List.length l1<>List.length l2 then raise Not_unifiable else
List.fold_left2(fun acc t1 t2->mgu(substitute_in_term acc t1)(substitute_in_term acc t2))Substitution.empty l1 l2


(* 15 points *)
assert (string_of_substitution (mgu (var_t "X") (var_t "Y")) = "{; X -> Y}" ||
        string_of_substitution (mgu (var_t "X") (var_t "Y")) = "{; Y -> X}");
assert (string_of_substitution (mgu (var_t "Y") (var_t "X")) = "{; X -> Y}" ||
        string_of_substitution (mgu (var_t "Y") (var_t "X")) = "{; Y -> X}");
assert (mgu (var_t "Y") (var_t "Y") = Substitution.empty);
assert (mgu (const_t "0") (const_t "0") = Substitution.empty);
assert (mgu (const_t "0") (var_t "Y") = Substitution.singleton (var "Y") (const_t "0"));
assert (
  match mgu (const_t "0") (const_t "1") with
  | _ -> false 
  | exception Not_unifiable -> true);
assert (
  match mgu (func_t "f" [const_t "0"]) (func_t "g" [const_t "1"]) with
  | _ -> false 
  | exception Not_unifiable -> true);
assert (mgu (func_t "f" [var_t "X"]) (func_t "f" [var_t "Y"]) = Substitution.singleton (var "X") (var_t "Y") ||
        mgu (func_t "f" [var_t "X"]) (func_t "f" [var_t "Y"]) = Substitution.singleton (var "Y") (var_t "X"))

(* 15 points *)
let t1 = F (Function("f", [V (Variable "X"); V (Variable "Y"); V (Variable "Y")])) in 
let t2 = F (Function("f", [V (Variable "Y"); V (Variable "Z"); V (Variable "a")])) in
let u = mgu t1 t2 in
assert (Substitution.cardinal u = 3);
assert (string_of_substitution u = "{; X -> a; Y -> a; Z -> a}");







let rec query ?(limit=10) program goal = 
   

(* 10 points *)
let p = [fact @@ pred "f" [const_t "a"; const_t "b"]] in
let g = [pred "f" [const_t "a"; const_t "b"]] in
let g' = match query p g with [v] -> v | _ -> failwith "error" in
assert (g' = g)

(* 10 points *)
let p = [fact @@ pred "f" [const_t "a"; const_t "b"]] in
let g = [pred "f" [const_t "a"; const_t "c"]] in
assert (query p g = [])

(* 10 points *)
let p = [fact @@ pred "f" [const_t "a"; const_t "b"]] in
let g = [pred "f" [var_t "X"; const_t "b"]] in
let g' = match query p g with [v] -> v | _ -> failwith "error" in
assert (g' = [pred "f" [const_t "a"; const_t "b"]]);

let g = [pred "f" [var_t "X"; var_t "Y"]] in
let g' = match query p g with [v] -> v | _ -> failwith "error" in
assert (g' = [pred "f" [const_t "a"; const_t "b"]])

(* 10 points *)
let ancestor x y = pred "ancestor" [x;y] in
let father x y = pred "father" [x;y] in
let father_consts x y =  father (C (Constant x)) (C (Constant y)) in

let f1 = Fact (father_consts "rickard" "ned") in
let f2 = Fact (father_consts "ned" "robb") in
let r1 = Rule (ancestor (var_t "X") (var_t "Y"), [father (var_t "X") (var_t "Y")]) in
let r2 = Rule (ancestor (var_t "X") (var_t "Y"), [father (var_t "X") (var_t "Z"); ancestor (var_t "Z") (var_t "Y")]) in

let p = [f1;f2;r1;r2] in
let g = [ancestor (const_t "rickard") (const_t "ned")] in
let g' = match query p g with [v] -> v | _ -> failwith "error" in
assert (g' = g)

(* 20 points *)
(* Tests backtracking *)
let ancestor x y = pred "ancestor" [x;y] in
let father x y = pred "father" [x;y] in
let father_consts x y =  father (C (Constant x)) (C (Constant y)) in

let f1 = Fact (father_consts "rickard" "ned") in
let f2 = Fact (father_consts "ned" "robb") in
let r1 = Rule (ancestor (var_t "X") (var_t "Y"), [father (var_t "X") (var_t "Y")]) in
let r2 = Rule (ancestor (var_t "X") (var_t "Y"), [father (var_t "X") (var_t "Z"); ancestor (var_t "Z") (var_t "Y")]) in

let p = [f1;f2;r1;r2] in

let g = [ancestor (const_t "rickard") (const_t "robb")] in
let g' = match query p g with [v] -> v | _ -> failwith "error" in
assert (g' = g)

(* 15 points *)
(* Tests choice points *)
let ancestor x y = pred "ancestor" [x;y] in
let father x y = pred "father" [x;y] in
let father_consts x y =  father (C (Constant x)) (C (Constant y)) in

let f1 = Fact (father_consts "rickard" "ned") in
let f2 = Fact (father_consts "ned" "robb") in
let r1 = Rule (ancestor (var_t "X") (var_t "Y"), [father (var_t "X") (var_t "Y")]) in
let r2 = Rule (ancestor (var_t "X") (var_t "Y"), [father (var_t "X") (var_t "Z"); ancestor (var_t "Z") (var_t "Y")]) in

let p = [f1;f2;r1;r2] in

let g = [ancestor (var_t "X") (const_t "robb")] in
let g1,g2 = match query p g with [v1;v2] -> v1,v2 | _ -> failwith "error" in
assert (g1 = [ancestor (const_t "ned") (const_t "robb")]);
assert (g2 = [ancestor (const_t "rickard") (const_t "robb")])

(* 15 points *)
(* Tests choice points *)
let nil = const_t "nil" in
let cons h t = func_t "cons" [h;t] in
let append x y z = pred "append" [x;y;z] in
let c1 = fact @@ append nil (var_t "Q") (var_t "Q") in
let c2 = rule (append (cons (var_t "H") (var_t "P")) (var_t "Q") (cons (var_t "H") (var_t "R")))
              [append (var_t "P") (var_t "Q") (var_t "R")] in
let p = [c1;c2] in

let g = [append (var_t "X") (var_t "Y") (cons (const_t "1") (cons (const_t "2") (cons (const_t "3") nil)))] in

let g' = query p g in
assert (List.length g' = 4)






