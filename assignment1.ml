let name = ""
let rollno = ""

let rec cond_dup l f =
match l with
[]->[]|
[h]->if f h then h::l else l|
h::t->if f h then h::h::cond_dup t f else h::cond_dup t f;;
  


(* 10 points *)
assert (cond_dup [3;4;5] (fun x -> x mod 2 = 1) = [3;3;4;5;5])

let rec n_times (f, n, v) =
if n<=0 then  v else n_times (f,(n-1),f v);;

  


(* 10 points *)
assert (n_times((fun x-> x+1), 50, 0) = 50)

exception IncorrectRange

let rec range num1 num2 =
if num2 < num1 then raise IncorrectRange else if num2=num1 then num1::[]else    num1::range (num1+1) num2;;

(* 10 points *)
assert (range 2 5 = [2;3;4;5])

let rec zipwith f l1 l2 =
match l1,l2 with
h1::t1,h2::t2->f h1 h2::zipwith f t1 t2|
_,_->[]
 

(* 10 points *)
assert (zipwith (+) [1;2;3] [4;5] = [5;7]) 

let rec insert_into_buckets eq x buckets =
 match buckets with
 []->[[x]]|
 h::t->if eq x (List.hd h) then (h@[x])::t else h::insert_into_buckets eq x t

let buckets p l =
List.fold_left (fun acc x -> insert_into_buckets p x acc) [] l

(* 20 points *)
assert (buckets (=) [1;2;3;4] = [[1];[2];[3];[4]])
; assert (buckets (=) [1;2;3;4;2;3;4;3;4] = [[1];[2;2];[3;3;3];[4;4;4]])
; assert (buckets (fun x y -> (=) (x mod 3) (y mod 3)) [1;2;3;4;5;6] = [[1;4];[2;5];[3;6]])

let remove_stutter l =
let rec rs l prev=
  match l with 
  []->[]|
  h::t->if h!=prev then h::rs t h else rs t h
  in rs l 0;;
  


(* 15 points *)
assert (remove_stutter [1;2;2;3;1;1;1;4;4;2;2] = [1; 2; 3; 1; 4; 2]) 

let rec flatten l =
  match l with 
  []->[]|
  [h]->h|
  h::t->h @ flatten t ;;
  
  

(* 10 points *)
assert (flatten ([[1;2];[3;4]]) = [1;2;3;4])

type 'a tree = Leaf | Node of 'a tree * 'a * 'a tree



let rec fold_inorder f acc t =match t with 
Leaf->acc|
Node(l,v,r)->let left=fold_inorder f acc l in
let value=f left v in
fold_inorder f value r;;

let rec fold_preorder f acc t=match t with
Leaf->acc|
Node(l,v,r)->let value=f acc v in
let left=fold_preorder f value l in
fold_preorder f left r

let rec fold_postorder f acc t=match t with 
Leaf->acc|
Node(l,v,r)->let left=fold_postorder f acc l in
let right=fold_postorder f left r in
f right v

(* 15 points *)
assert (fold_inorder (fun acc x -> acc @ [x]) [] (Node (Node (Leaf,1,Leaf), 2, Node (Leaf,3,Leaf))) = [1;2;3]) 

let fib_tailrec n =
  let rec fib n prev cur=
  if n=0 then prev
  else if n=1 then cur
 else  fib (n-1) (cur) (prev+cur) in 
 fib n 0 1;;


(* 15 points *)
assert (fib_tailrec 50 = 12586269025)


