let name = "Sandra"
let rollno = ""

module type FHEAP = sig
  type ('k,'v) t
  val empty_heap : ('k,'v) t
  val set        : ('k,'v) t -> 'k -> 'v -> ('k,'v) t
  val get        : ('k,'v) t -> 'k -> 'v option
end

module FHeap : FHEAP = struct
  type ('k,'v) t = 'k -> 'v option
  let empty_heap = fun k -> None
  let set h x v = fun k -> if k = x then Some v else h k
  let get h x = h x
end

let open FHeap in 
let h = empty_heap in
let h = set h 0 "Hello" in
let h = set h 1 "World" in
Printf.printf "%s %s\n%!" (Option.get (get h 0)) (Option.get (get h 1));
let h = set h 1 "CS3100 students" in
Printf.printf "%s %s\n%!" (Option.get (get h 0)) (Option.get (get h 1))

module type MONAD = sig
  type 'a t
  val return : 'a -> 'a t
  val (let*)  : 'a t -> ('a -> 'b t) -> 'b t
end

module type REF_MONAD = sig
  type value   (* type of value *)
  type ref     (* type of reference *)
  include MONAD
  val mk_ref : value -> ref t
  val (!) : ref -> value t
  val (:=) : ref -> value -> unit t
  val run_state : 'a t -> 'a
end

module Ref_monad (V : sig type t end) : REF_MONAD with type value = V.t = struct
  type value = V.t
  type ref = int  (* Just an index into the heap *)
  
  type 'a t = 
    int * (int, value) FHeap.t ->  (* Takes counter + heap *)
    int * (int, value) FHeap.t * 'a  (* Returns updated counter, heap, and result *)

  (* return: Does not modify state, just returns a value *)
  let return x = fun state -> (state, x)

  (* bind: Threads state implicitly *)
  let (let*) m f = fun state ->
    let (new_state, x) = m state in
    f x new_state

  (* mk_ref: Creates a new reference *)
  let mk_ref v = fun (counter, heap) ->
    let new_ref = counter in
    let new_heap = FHeap.set heap new_ref v in
    ((counter + 1, new_heap), new_ref)  (* Returns new reference *)

  (* Read value from reference *)
  let (!) r = fun (counter, heap) ->
    match FHeap.get heap r with
    | Some v -> ((counter, heap), v)
    | None -> failwith "Invalid reference"

  (* Write new value to reference *)
  let (:=) r v = fun (counter, heap) ->
    let new_heap = FHeap.set heap r v in
    ((counter, new_heap), ())

  (* Run state monad with empty heap and counter=0 *)
  let run_state m =
    let (_, _, result) = m (0, FHeap.empty_heap) in
    result
end


(* 5 points *)
let module R = Ref_monad(struct type t = int end) in
let open R in
let module M = struct
  let program = 
    let* i = mk_ref 10 in
    !i
end
in assert (run_state M.program = 10)


(* 5 points *)
let module R = Ref_monad(struct type t = int end) in
let open R in 
let module M = struct
  let program = 
    let* i = mk_ref 10 in
    let* iv = !i in
    let* _ = (i := iv + 1) in
    !i
  end 
in assert (run_state M.program = 11)


(* 10 points *)
let module R = Ref_monad(struct type t = int end) in
let open R in
let module M = struct
  let program = 
    let* i = mk_ref 10 in
    let* j = mk_ref 20 in
    let* iv = !i in
    let* _ = i := iv + 1 in
    let* jv = !j in
    let* iv = !i in
    return (iv + jv)
end
in assert(run_state M.program = 31)


module Univ : sig
  type t
  type 'a packer = {pack : 'a -> t; unpack : t -> 'a option}
  val mk : unit -> 'a packer
end = struct
  type t = exn
  type 'a packer = {pack : 'a -> t; unpack : t -> 'a option}
  let mk : type a. unit -> a packer = fun () ->
    let module M () = struct exception E of a end in
    let module F = M () in
    {pack = (fun v -> F.E v); 
     unpack = fun p -> match p with F.E v -> Some v | _ -> None}
end

module M = struct
  include Univ
  let int_packer = mk ()
  let float_packer = mk ()
  
  let l = [int_packer.pack 10; float_packer.pack 20.25]
  
  let rec get packer l =
    match l with
    | [] -> None
    | x::xs -> 
        match packer.unpack x with
        | Some v -> Some v
        | None -> get packer xs
end;;

M.get M.int_packer M.l;;
M.get M.float_packer M.l


module type POLY_REF_MONAD = sig
  type 'a ref (* type of reference *)
  include MONAD
  val mk_ref : 'a -> 'a ref t
  val (!) : 'a ref -> 'a t
  val (:=) : 'a ref -> 'a -> unit t
  val run_state : 'a t -> 'a
end

module Poly_ref_monad : POLY_REF_MONAD = struct
  type 'a ref = int * 'a Univ.packer
  type 'a t = int * (int, Univ.t) FHeap.t -> int * (int, Univ.t) FHeap.t * 'a

  (* Implement the missing functions *)

(* YOUR CODE HERE *)
raise (Failure "Not implemented")
end

(* 10 points *)
let module M = struct
  open Poly_ref_monad

  let program = 
    let* i = mk_ref 10 in
    let* s = mk_ref "20" in
    return ()
  end 
in assert (Poly_ref_monad.run_state M.program = ())


(* 10 points *)
let open Poly_ref_monad in
let module M = struct
  let program = 
    let* i = mk_ref 10 in
    let* s = mk_ref "20" in
    let* iv = !i in
    let* _ = i := iv + 1 in
    let* sv = !s in
    let* iv = !i in
    return (iv + int_of_string sv)
end
in assert (run_state M.program = 31)


type 'a stream = Cons of 'a * 'a stream Lazy.t

let hd (Cons(x,_)) = x
let tl (Cons(x,xs)) = Lazy.force xs
let rec take n s =
  if n = 0 then []
  else hd s::(take (n-1) (tl s))


let pow2 = let rec pow n=
Cons(n,lazy(pow(2*n))) in
pow 1
 

(* 10 points *)
assert (List.hd (List.rev (take 10 pow2)) = 512)

let rec interleave s1 s2 =
let (Cons(x,xs))=s1 in
let (Cons(y,ys))=s2 in
Cons(x,lazy(Cons(y,lazy(interleave (Lazy.force(xs))(Lazy.force(ys))))))

  


(* 15 points *)
let rec zeros = Cons(0,lazy zeros) in
let rec ones = Cons(1,lazy ones) in
assert (take 10 (interleave zeros ones) = [0; 1; 0; 1; 0; 1; 0; 1; 0; 1])



let rec fact n=if n=0. then 1. else n*.fact(n-.1.);;
let e_terms x =
  let rec tay k =
    let v= (x ** float_of_int k) /. fact (float_of_int k) in
    Cons (v, lazy (tay (k + 1)))
  in tay 0 

  

(* 10 points *)
assert (Float.round(List.hd (List.rev (take 10 (e_terms 1.0))) *. (10. ** 9.)) = 2756.)

let total (Cons(x,xs)) = 
let rec tt sum (Cons(y,ys))=Cons(sum,lazy(tt(sum+.y)(Lazy.force ys))) in
tt x (Lazy.force xs)


(* 15 points *)
let rec f x = Cons (x, lazy (f (x+.1.0))) in
assert (take 10 (total (f 1.0)) = [1.; 3.; 6.; 10.; 15.; 21.; 28.; 36.; 45.; 55.])

let rec within eps s =
let Cons(x,xs)=s in 
let Cons(y,ys)=Lazy.force(xs) in
if abs_float(x-.y)<eps then y else
within eps (Cons(y,ys))


(* 20 points *)
assert (Float.round(within 1e-15 (total (e_terms 1.0)) *. (10. ** 3.)) = 2718.)

let e x eps = 
let e_ser=total(e_terms x) in
within eps (tl e_ser)



(* 10 points *)
assert (Float.round (e 1.0 1e-15 *. (10. ** 6.)) = 2718282.)


