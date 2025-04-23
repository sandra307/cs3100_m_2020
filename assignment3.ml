let name = ""
let rollno = ""

module type Showable = sig
  type t
  val string_of_t : t -> string
end

module IntShowable=struct
type t=int
let string_of_t f=Int.to_string(f)
end
module FloatShowable=struct
type t=float
let string_of_t f=Float.to_string(f)
end

(* 15 points *)
assert (IntShowable.string_of_t 10 = "10");
assert (FloatShowable.string_of_t 0.0 = "0.")

module type DoublyLinkedListNode = sig
  type t
  (** The type of doubly linked list node *)
  
  type content
  (** The type of content stored in the doubly linked list node *)

  val create : content -> t 
  (** create a new doubly linked list node with [content] as the content. 
      The next and previous nodes are [None]. *)
  
  val get_next : t -> t option
  (** [get_next t] returns [Some t'] if [t'] is the successor node of [t]. 
      If [t] has no successor, then return [None] *)
      
  val get_prev : t -> t option
  (** [get_prev t] returns [Some t'] if [t'] is the predecessor node of [t]. 
      If [t] has no predecessor, then return [None] *)
      
  val get_content : t -> content
  (** [content t] returns the content [c] of node [t] *)
      
  val set_next : t -> t option -> unit
  (** [set_next t t'] updates the next node of [t] to be [t'] *)
  
  val set_prev : t -> t option -> unit
  (** [set_prev t t'] updates the prev node of [t] to be [t'] *)
  
  val string_of_content : content -> string
  (** [string_of_content c] returns the string form of content [c] *)
end

(* Implement the functor MakeNode *)


module MakeNode (C : Showable) : DoublyLinkedListNode with type content = C.t = struct
(*type  node={
mutable prev:'a node option;
value:'a;
mutable next:'a node option
}
type t= node
type content=C.t
let create v={prev=None;value=v;next=None}
let get_next n=n.next
let get_prev n=n.prev
let get_content n=n.value
let set_next n a=n.next<-a
let set_prev n a=n.prev<-a
let string_of_content v=Int.to_string(v)*)
 type content = C.t

  type node= {
    mutable next : node option;
    mutable prev : node option;
    content : content;
  }
  type t=node

  let create c = { next = None; prev = None; content = c }
  
  let get_next n = n.next
  let get_prev n = n.prev
  let get_content n = n.content
  
  let set_next n a = n.next <- a
  let set_prev n a = n.prev <- a

  let string_of_content v= C.string_of_t v


end

module IntNode = MakeNode(IntShowable)

(* 15 points *)
let open IntNode in 
let i1 = create 1 in
assert (get_content i1 = 1)

(* 15 points *)
let open IntNode in 
let i1,i2,i3 = create 1, create 2, create 3 in
set_next i1 @@ Some i2;
set_next i2 @@ Some i3;
set_prev i2 @@ Some i1;
set_prev i3 @@ Some i2;
let _ = assert (match get_next i1 with None -> false | Some i2 -> get_content i2 = 2) in
()

module type DoublyLinkedList = sig
  type t 
  (** The type of doubly linked list *)
  
  type node
  (** The type of a doubly linked list node *)
  
  type content
  (** The type of content stored in the [node] of doubly linked list *)
    
  val create : unit -> t 
  (** Creates a new doubly linked list *)
  
  val assign : t -> node option -> unit
  (** [assign t n] makes the node as the head node of the list. 
      The original contents of the list are dropped. *)
  
  val t_of_list : content list -> t
  (** [t_of_list l] returns a new doubly linked list with the list of 
      elements from the list [l]. *)
  
  val is_empty : t -> bool
  (** [is_empty l] return true if [t] is empty *)
  
  val first : t -> node option
  (** [first l] return [Some n] if the list is non-empty. Otherwise, return [None] *)
  
  val insert_first : t -> content -> node
  (** [insert_first l c] inserts a new doubly linked list node [n] as the first 
      node in [l] with [c] as the content. Returns [n]. *)
      
  val insert_after : node -> content -> node
  (** [insert_after n c] inserts a new node [n'] with content [c] after the node [n].
      Returns [n']. *)
  
  val remove : t -> node -> unit
  (** [remove l n] removes the node [n] from the list [l] *)
  
  val iter : t -> (content -> unit) -> unit
  (** [iter l f] applies [f] to each element of the list in the list order. *)
  
  val iter_node : t -> (node -> unit) -> unit
  (** [iter_node l f] applies [f] to each node of the list in the list order. 
      [f] may delete the current node or insert a new node after the current node. 
      In either case, [iter_node] is applied to the rest of the original list. *)
      
  val string_of_t : t -> string
  (** [string_of_t (t_of_list [1;2;3])] returns the string "[1->2->3]".
      [string_of_t (t_of_list [])] returns the string "[]" *)
end

(* Implement the functor MakeList *)


module MakeList (N : DoublyLinkedListNode) : DoublyLinkedList with type content = N.content and type node=N.t=
                                                               
struct

type node = N.t
type content = N.content

type t = {mutable head: node option}
let create () = {head = None}

 let assign t n = t.head <-n

  let t_of_list lst =
    let l = create () in
    let rec aux prev = function
      | [] -> ()
      | x :: xs ->
        let n = N.create x in
        (match prev with
         | Some p -> N.set_next p (Some n); N.set_prev n (Some p)
         | None -> l.head <- Some n);
        aux (Some n) xs
    in
    aux None lst;
    l

let is_empty t = (t.head=None)

let first l = l.head



let insert_first l c = 
let n = N.create c in 
(match l.head with 

|Some e ->
N.set_next n (Some e);
N.set_prev e (Some n);
        
|None -> ());
l.head<- Some n;
n


  let insert_after n c =
    let new_node = N.create c in
    let next_node = N.get_next n in
      N.set_next n (Some new_node);
    
    N.set_prev new_node (Some n);
    (match next_node with
     | Some next -> N.set_prev next (Some new_node);
                      N.set_next new_node  next_node;
     | None -> ());
 
    new_node
    

    
    
let remove l n = let np=N.get_prev n in
let nn=N.get_next n in
(match np with 
Some e -> N.set_next e nn ;
|None -> l.head <-nn);

(match nn with
 Some p ->N.set_prev p np;   
|    None ->());
 N.set_prev n None;
   N.set_next n None

   
   
 

           
    let iter l f = 
let rec ux =function 
    |None ->() 
    |Some e -> f (N.get_content e) ;ux (N.get_next e) 
in 
ux l.head


let iter_node l f = 
let rec loop = 
function 
None ->()|
Some e ->f e;loop(N.get_next e) in loop l.head

  let string_of_t l =
  N.string_of_content

end






(* 10 points *)
let module L = MakeList(IntNode) in

let open L in
assert (is_empty (t_of_list []));
let l = t_of_list [1;2;3] in
assert (not @@ is_empty l);
let n = match first l with 
| None -> failwith "impossible" 
| Some n -> n
in
assert (1 = IntNode.get_content n);
L.(assign l (first (t_of_list [4;5;6])));
match first l with
| None -> failwith "impossible"
| Some n -> assert (IntNode.get_content n = 4)


(* 10 points *)
let module L = MakeList(IntNode) in

let open L in
let l = t_of_list [1;2;3] in
let n1 = match first l with
  | Some n1 -> n1
  | None -> failwith "impossible"
in
let n2 = match IntNode.get_next n1 with
  | Some n2 -> n2
  | None -> failwith "impossible"
in
remove l n2;
let n3 = match IntNode.get_next n1 with
  | Some n3 -> n3
  | None -> failwith "impossible"
in
let _ = assert (IntNode.get_content n3 = 3) in
remove l n1;
match first l with
| None -> failwith "impossible"
| Some n3 -> assert (IntNode.get_content n3 = 3)


(* 15 points *)
let module L = MakeList(IntNode) in
let open L in
let l = t_of_list [1;2;3] in
let s = ref 0 in
iter l (fun c -> s := !s + c);
assert (!s = 6);
iter_node l (fun n -> if IntNode.get_content n mod 2 == 0 then remove l n);
let n1 = match first l with
  | None -> failwith "impossible"
  | Some n -> n
in
assert (IntNode.get_content n1 = 1)


module type Dll_functions = sig
  type dll
  (** The type of doubly linked list *)
  
  type node
  (** The type of doubly linked list node *)
  
  type content
  (** The type of doubly linked list content *)

  val length : dll -> int
  (** Returns the length of the list. 
      Use [DLL.iter] to implement it. *)
  
  val duplicate : dll -> unit
  (** Given a doubly linked list [l] = [1->2], [duplicate l] returns [1->1->2->2]. 
      Use [DLL.iter_node] to implement it. *)
        
  val rotate : dll -> int -> unit
  (** [rotate l n] rotates the list by [n] nodes. 
      If the list is [1->2->3->4->5], then [rotate l 0] will not modify the list. 
      [rotate l 2] will modify the list to be [3->4->5->1->2]. 
      Assume that [0 <= n < length l]. *)
  
   val reverse : dll -> unit
   (** [reverse l] reverses the list *)
end

module MakeDllFunctions (N : DoublyLinkedListNode) 
  : Dll_functions with type node = N.t 
                   and type content = N.content 
                   and type dll = MakeList(N).t = struct

end

(* 10 points *)
let module F = MakeDllFunctions (IntNode) in
let module M = MakeList(IntNode) in
let open M in 
let l = t_of_list [1;2;3] in
let _ = assert (F.length l = 3) in
F.duplicate l;
let _ = assert (F.length l = 6) in
()

(* 10 points *)
let module F = MakeDllFunctions (IntNode) in
let module M = MakeList(IntNode) in
let open M in 
let l = t_of_list [1;2;3] in
let _ = assert (F.length l = 3) in
F.duplicate l;
let _ = assert (F.length l = 6) in
let _ = assert ("[1->1->2->2->3->3]" = string_of_t l) in
F.rotate l 3;
let _ = assert ("[2->3->3->1->1->2]" = string_of_t l) in
F.rotate l 0;
let _ = assert ("[2->3->3->1->1->2]" = string_of_t l) in
let l = t_of_list [] in
F.rotate l 0;
let _ = assert ("[]" = string_of_t l) in
()

(* 10 points *)
let module F = MakeDllFunctions (IntNode) in
let module M = MakeList(IntNode) in
let open M in 
let l = t_of_list [1;2;3] in
F.reverse l;
assert ("[3->2->1]" = string_of_t l)


module type Key = sig
  type t
  (** The type of key *)
  
  val num_buckets : int
  (** The number of buckets i.e, the size of the buckets array *)
  
  val hash : t -> int
  (** Hashes the key to an integer between [0, num_buckets) *)
  
  val string_of_t : t -> string
  (** Returns the string representation of key *)
end

module type Hash_table = sig
  type key
  (** The type of key *)
  
  type content
  (** The type of value *)
  
  type t
  (** The type of the hash table *)
  
  val create : unit -> t
  (** Creates a new hash table *)
  
  val put :  t -> key -> content -> unit
  (** [put h k v] associates the key [k] with value [v] in the hash table [h]. 
      If the binding for [k] already exists, overwrite it. *)

  val get : t -> key -> content option
  (** [get h k] returns [Some v], where [v] is the value associated with the 
      key [k] in the hash table [h]. Returns [None] if the [k] is not bound in [h]. *)
      
  val remove : t -> key -> unit
  (** [remove h k] removes the association for key [k] from the hash table [h] if it exists *)
  
  val length : t -> int
  (** Return the number of key-value pairs in the hash table *)
  
  val string_of_t : t -> string
  (** Returns a string version of the hash table. Can be in any format. Only for debugging. *)
  
  val chain_length : t -> int -> int
  (** [chain_length h bucket] returns the length of the doubly linked list 
      at the index [bucket] in the underlying array. 
      Assume that [0 <= bucket < length(bucket_array)] *)
end

(* Implement the functor Make_hash_table *)

(* YOUR CODE HERE *)
raise (Failure "Not implemented")

#show_module_type Key

module K : Key with type t = int = struct
  type t = int
  let num_buckets = 64
  let hash k = k mod num_buckets
  let string_of_t = string_of_int
end

module StringShowable : Showable with type t = string = struct
  type t = string
  let string_of_t s = s
end

module H = Make_hash_table(K)(StringShowable)

open H

(* 15 points *)
let h = create () in
put h 0 "zero";
put h 1 "one";
assert (get h 0 = Some "zero");
assert (get h 1 = Some "one");
put h 0 "-zero-";
assert (get h 0 = Some "-zero-")


(* 20 points *)
let h = create () in
put h 0 "zero";
put h 1 "one";
assert (get h 0 = Some "zero");
assert (get h 1 = Some "one");
put h 64 "-zero-";
assert (get h 0 = Some "zero");
assert (get h 64 = Some "-zero-");
assert (length h = 3);
assert (chain_length h 0 = 2);
assert (chain_length h 1 = 1)

