let name = "Sandra"
let rollno = ""

#use "init.ml"
open Syntax
let parse_string = Lambda_parse.parse_string
let string_of_expr = string_of_expr

let _ = parse_string "(\\x.x) (\\y.y)"
let _ = string_of_expr (App (Var "x",Lam("y",App(Var "y", Var "x"))))

let mem e l = 
let rec mem e l=
match l with []->false|
x::xs->if x=e then true else mem e xs in mem e l;;

(* 5 points *)
assert (mem "b" ["a";"b";"c"] = true);
assert (mem "x" ["a";"b";"c"] = false)

let remove e l =if l=[]then [] else List.filter(fun x->x<>e)l;;
 

(* 5 points *)
assert (remove "b" ["a";"b";"c"] = ["a";"c"]);
assert (remove "x" ["a";"b";"c"] = ["a";"b";"c"])

assert (List.sort String.compare ["x";"a";"b";"m"] = ["a";"b";"m";"x"])

let remove_stutter l =
let rec rs l prev=
  match l with 
  []->[]|
  h::t->if (String.equal h  prev)=false then h::rs t h else rs t h
  in rs l "";;
let union l1 l2 =
match l2 with
[]->remove_stutter(List.sort String.compare l1)|
_->remove_stutter(List.sort String.compare(List.append l1 l2));;
 

(* 5 points *)
assert (union ["a"; "c"; "b"] ["d"; "b"; "x"; "a"] = ["a"; "b"; "c"; "d"; "x"])

let add e l = 
 match l with 
 []->e::[]|
 _->if List.exists(fun x->if e=x then true else false)l then List.sort String.compare l else List.sort String.compare (e::l);;

(* 5 points *)
assert (add "b" ["a";"c"] = ["a";"b";"c"]);
assert (add "a" ["c"; "a"] = ["a";"c"])

let r = ref 0                                                                       
                                                                                    
let fresh s =                                                                       
  let v = !r in                                                                     
  r := !r + 1;                                                                      
  s ^ (string_of_int v)

let a = fresh "a"
let b = fresh "b"


let rec rd l=match l with
[]->[]|
h::t->if List.mem h t then rd t else h::rd t;;
let rec free_variables e = match e with
Var x->[x]|
Lam(x,exp)->List.filter(fun f->f<>x)(free_variables exp)|
App(first,second)->rd(free_variables first@free_variables second);;
  

(* 20 points *)
assert (free_variables (parse_string "\\x.x") = []);
assert (free_variables (parse_string "\\x.y") = ["y"])

let rec rename_var e o n=
match e with 
Var x->if x=o then Var n else Var x|
Lam(x,y)->if x=o then Lam(o,rename_var y o n) else Lam(x,rename_var y o n)|
App(x,y)->App(rename_var x o n,rename_var y o n)


let rec substitute expr a b =
match expr with 
Var x->if x=a then b else Var x|
Lam(x,y)->if x=a then Lam(x,y) 
else if not(List.mem x (free_variables b))then Lam(x,substitute y a b)
else let x'=fresh x in
let y'=rename_var y x x' in
Lam(x',substitute y' a b)|
App(fst,snd)->App(substitute fst a b,substitute snd a b)


(* 20 points *)
assert (alpha_equiv 
          (substitute (parse_string "\\y.x") "x" (parse_string "\\z.z w")) 
          (parse_string "λy.λz.z w"));
assert (alpha_equiv 
          (substitute (parse_string "\\x.x") "x" (parse_string "y"))
          (parse_string "λx.x"));
assert (alpha_equiv 
          (substitute (parse_string "\\x.y") "y" (parse_string "x"))
          (parse_string "λx0.x"))

let is_value e =
  match e with
  | Lam (_, _) -> true
  | _ -> false

let rec reduce_cbv e =

 match e with
 App(Lam(x,b),v) when is_value v->
 Some(substitute b x v)
| App(u,f) when not(is_value u)->
 begin
 match reduce_cbv u with
 Some e'->Some(App(e',f))|
 None->None
 end
 |App(v,f) when (is_value v)&&not(is_value f)->
 begin
 match reduce_cbv f with
 Some f'->Some(App(v,f'))|
 None->None
 end
 |_->None
 
 
 

(* 20 points *)
begin match reduce_cbv (parse_string "(\\x.x) ((\\x.x) (\\z.(\\x.x) z))") with
| Some expr -> assert (alpha_equiv expr (parse_string "(λx.x) (λz.(λx.x) z)"))
| None -> assert false
end;
        
begin match reduce_cbv (parse_string "(λx.x) (λz.(λx.x) z)") with
| Some expr -> assert (alpha_equiv expr (parse_string "λz.(λx.x) z"))
| None -> assert false
end;
        
assert (reduce_cbv (parse_string "λz.(λx.x) z") = None);
        
begin match reduce_cbv (parse_string "(λx.y) ((λx.x x) (λx.x x))") with
| Some expr -> assert (alpha_equiv expr (parse_string "(λx.y) ((λx.x x) (λx.x x))"))
| None -> assert false
end;

assert (reduce_cbv (parse_string "x y z") = None)


let rec reduce_cbn e =match e with 
App(Lam(x,b),v)->Some(substitute b x v)|
App(r,u)->begin 
match reduce_cbn r with
Some(r')->Some(App(r',u))|
None->None
end
|_->None




(* 20 points *)
begin match reduce_cbn (parse_string "(\\x.x) ((\\x.x) (\\z.(\\x.x) z))") with
| Some expr -> assert (alpha_equiv expr (parse_string "(λx.x) (λz.(λx.x) z)"))
| None -> assert false
end;
        
begin match reduce_cbn (parse_string "(λx.x) (λz.(λx.x) z)") with
| Some expr -> assert (alpha_equiv expr (parse_string "λz.(λx.x) z"))
| None -> assert false
end;
        
assert (reduce_cbn (parse_string "λz.(λx.x) z") = None);
        
begin match reduce_cbn (parse_string "(λx.y) ((λx.x x) (λx.x x))") with
| Some expr -> assert (alpha_equiv expr (parse_string "y"))
| None -> assert false
end;

begin match reduce_cbn (parse_string "(\\x.x x) ((\\z.z) y)") with
| Some expr -> assert (alpha_equiv expr (parse_string "(λz.z) y ((λz.z) y)"))
| None -> assert false
end;

assert (reduce_cbn (parse_string "x y z") = None)


let rec reduce_normal e =
  match e with
  | App (Lam (x, b), v) ->
      
      Some (substitute b x v)
  | App (e1, e2) ->
      
      begin
        match reduce_normal e1 with
        | Some e1' -> Some (App (e1', e2))
        | None ->
            match reduce_normal e2 with
            | Some e2' -> Some (App (e1, e2'))
            | None -> None
      end
  | Var _ -> None
  | Lam _ -> None

(* 20 points *)
begin match reduce_normal (parse_string "(\\x.x) ((\\x.x) (\\z.(\\x.x) z))") with
| Some expr -> assert (alpha_equiv expr (parse_string "(λx.x) (λz.(λx.x) z)"))
| None -> assert false
end;
        
begin match reduce_normal (parse_string "(λx.x) (λz.(λx.x) z)") with
| Some expr -> assert (alpha_equiv expr (parse_string "λz.(λx.x) z"))
| None -> assert false
end;
        
begin match reduce_normal (parse_string "λz.(λx.x) z") with
| Some expr -> assert (alpha_equiv expr (parse_string "λz. z"))
| None -> assert false
end;
        
begin match reduce_normal (parse_string "(λx.y) ((λx.x x) (λx.x x))") with
| Some expr -> assert (alpha_equiv expr (parse_string "y"))
| None -> assert false
end;

begin match reduce_normal (parse_string "(\\x.x x) ((\\z.z) y)") with
| Some expr -> assert (alpha_equiv expr (parse_string "(λz.z) y ((λz.z) y)"))
| None -> assert false
end;
        
begin match reduce_normal (parse_string "f (\\x.x x) ((\\z.z) y)") with
| Some expr -> assert (alpha_equiv expr (parse_string "f (λx.x x) y"))
| None -> assert false
end;

begin match reduce_normal (parse_string "(\\x.(\\z.z) y) (\\x.x x)") with
| Some expr -> assert (alpha_equiv expr (parse_string "(λz.z) y"))
| None -> assert false
end


let rec eval log depth reduce expr =                     
  if depth = 0 then failwith "non-termination?"                                  
  else                                                                     
    begin match reduce expr with
    | None -> expr
    | Some expr' ->
      if log then print_endline ("= " ^ (string_of_expr expr'));                 
      eval log (depth-1) reduce expr'                                    
    end
  
let eval_cbv = eval true 1000 reduce_cbv
let eval_cbn = eval true 1000 reduce_cbn
let eval_normal = eval true 1000 reduce_normal

(* 10 points *)
let zero = parse_string "\\f.\\x. x" in
let one = parse_string "\\f.\\x. f x" in
let two = parse_string "\\f.\\x. f (f x)" in
let three = parse_string "\\f.\\x. f (f (f x))" in

let plus = parse_string "λm. λn. λs. λz. m s (n s z)" in
let mult = parse_string "λm. λn. λs. λz. m (n s) z" in

assert (alpha_equiv (eval_normal (App (App (plus, one), two))) three);
print_endline "";
assert (alpha_equiv (eval_normal (App (App (mult, one), three))) three);
print_endline "";
assert (alpha_equiv (eval_normal (App (App (mult, zero), three))) zero)


