let name = "Sandra"
let rollno = ""

type z = Z
type 'n s = S : 'n -> 'n s

(* scalar product of value with a list *)
let rec cross_v_l v l =
  match l with
  | [] -> []
  | x::xs -> (v,x)::cross_v_l v xs
  
let rec cross l1 l2 = 
  match l1 with
  | [] -> []
  | x::xs -> (cross_v_l x l2) @ cross xs l2

cross [1;2] ["a";"b";"c";"d"];;
cross [] [];;
cross [] [1];;
cross [1] ["a"];;

(* Length-indexed list *)
type (_,_) list =
  | Nil  : ('a, z ) list
  | Cons : 'a * ('a,'n) list -> ('a, 'n s) list


type ('a, 'n) list =
  | Nil
  | Cons of 'a * ('a, 'n) list
  
  let  cross_v_l v l =
  let rec cross1 v l=
  match l with
  | Nil -> Nil
  | Cons (x, xs) -> Cons ((v, x), cross1 v xs) in cross1 v l



 

(* 5 points *)
assert (cross_v_l 1 (Cons ("a", Cons ("b", Nil))) = Cons ((1, "a"), Cons ((1, "b"), Nil)))

let rec append l1 l2 =
  match l1 with
  | [] -> l2 
  | x::xs -> x::append xs l2


type (_,_,_) plus =
  | PlusZero  : (z,'n,'n) plus
  | PlusSucc : ('m, 'n s, 'o s) plus -> ('m s, 'n, 'o s) plus

  




(* 5 points *)
let zero_plus_zero_eq_zero : (z,z,z) plus = PlusZero

(* 5 points *)
let two_plus_three_eq_five : (z s s, z s s s, z s s s s s) plus = PlusSucc (PlusSucc PlusZero)

let rec append : type m n o. (m,n,o) plus -> ('a, m) list -> ('a, n) list -> ('a, o) list =


 

(* 10 points *)
assert (append zero_plus_zero_eq_zero Nil Nil = Nil);
assert (append two_plus_three_eq_five (Cons (1,Cons(2,Nil))) (Cons (3, Cons(4,Cons(5,Nil)))) 
        = Cons (1,Cons(2,Cons(3,Cons(4,Cons(5,Nil))))))
        



type (_,_,_) mult =
  | MultZero : (z, 'n, z) mult
  | MultSucc : ('n, 'p, 'o) plus * ('m, 'n, 'p) mult -> ('m s, 'n, 'o) mult
  




(* 5 points *)
let zero_mult_two_eq_zero : (z, z s s, z) mult = MultZero

(* 5 points *)
let one_mult_two_eq_two : (z s, z s s, z s s) mult = MultSucc (PlusSucc (PlusSucc PlusZero), MultZero)

let two_mult_two_eq_four : (z s s, z s s, z s s s s) mult =MultSucc(PlusSucc(PlusSucc(PlusSucc(PlusSucc PlusZero))),MultSucc(PlusSucc))


let two_mult_one_eq_two : (z s s, z s, z s s) mult =

  

(* 10 points *)
let _two_mult_two_eq_four : (z s s, z s s, z s s s s) mult = two_mult_two_eq_four in
let _two_mult_one_eq_two : (z s s, z s, z s s) mult = two_mult_one_eq_two in
()

let rec cross : type m n o. (m,n,o) mult -> ('a,m) list -> ('b,n) list -> ('a * 'b, o) list =
  

(* 20 points *)
assert (cross zero_mult_two_eq_zero Nil (Cons (1,Cons(2,Nil))) = Nil);
assert (cross one_mult_two_eq_two (Cons("a", Nil)) (Cons (1,Cons(2,Nil))) =
        Cons(("a",1), Cons(("a",2), Nil)))

let rec zip : type n. ('a,n) list -> ('b,n) list -> ('a *'b, n) list =
fun l1 l2->match l1, l2 with
|Nil,Nil->Nil|
Cons(x,xs),Cons(y,ys)->Cons((x,y),zip xs ys)

(* 10 points *)
assert (zip (Cons(1,Cons(2,Nil))) (Cons("a",Cons("b",Nil))) = 
        Cons((1,"a"), Cons((2,"b"), Nil)))



type (_,_,_) min =
  | MinZero1 : (z,'n,z)min
  | MinZero2 : ('m,z,z)min
  | MinSucc  : ('m,'n,'o)min->('m s,'n s,'o s)min




(* 10 points *)
let min_zero_four_zero : (z, z s s s s, z) min = MinZero1

let min_three_zero_zero : (z s s s, z, z) min = MinZero2


let min_three_five_eq_three : (z s s s, z s s s s s, z s s s) min = MinSucc(MinSucc(MinSucc MinZero1))
 

(* 10 points *)
let _min_three_zero_zero : (z s s s, z, z) min = min_three_zero_zero

let rec zip_matching : type n m o. (n,m,o) min -> ('a, n) list -> ('b, m) list -> ('a * 'b, o) list =
fun p l1 l2->
match p,l1,l2 with
|MinZero1,_,_->Nil
|MinZero2,_,_->Nil
|MinSucc s,Cons(x,xs),Cons(y,ys)->Cons((x,y),zip_matching s xs ys)


(* 15 points *)
assert (zip_matching min_zero_four_zero Nil (Cons(1,(Cons(2,Cons(3,Cons(4,Nil)))))) = Nil);
assert (zip_matching min_three_zero_zero  (Cons(1,(Cons(2,Cons(3,Nil))))) Nil = Nil)


