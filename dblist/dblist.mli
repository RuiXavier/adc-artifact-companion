type 'a innerNode = 
| Nil 
| Cons of 'a Node.node

type 'a dblist = {
  mutable head : 'a innerNode;
  mutable tail : 'a innerNode;
  mutable length : int;
}
(*@ mutable model view: 'a list*)

exception Empty

val create : unit -> 'a dblist
(*@ r = create ()
  ensures r.view = []*)

val is_empty : 'a dblist -> bool
(*@ b = is_empty list
  ensures b <-> list.view = [] *)

val clear : 'a dblist -> unit
(*@ clear list
  modifies list.view
  ensures list.view = []*)

  (*
(*Erro de tipificação*)  
val get_head_opt : 'a dblist -> 'a Node.node option
(*@ h = get_head_opt list
  ensures match list.view with
  | [] -> h = None
  | x::t -> h = Some (Node.create x) *) 

(* Como expressar que o retorno da função é ou a cabeça ou uma exceção? *)
val get_head : 'a dblist -> 'a Node.node
(*@ h = get_head list
  ensures match list.view with
          | [] -> raises Empty
          | x::_ -> h = x
  raises Empty -> list.view = []*) 

  *)
(* Como expressar que o retorno da função é o elemento final da lista? *)
val get_tail_opt : 'a dblist -> 'a Node.node option
val get_tail : 'a dblist -> 'a Node.node

val get_size : 'a dblist -> int
(*@ s = get_size list
  ensures s = List.length list.view *)

val insert_front : 'a dblist -> 'a -> unit
(*@ insert_front list data
    modifies list
    ensures list.view = data :: (old list.view) *)

val insert_back : 'a dblist -> 'a -> unit
(*@ insert_back list data
    modifies list
    ensures list.view = (old list.view) ++ (data::[]) *)

(*Como expressar que a nova data é inserida antes/depois da antiga data 
esteja ela onde estiver na lista, inicio, meio ou fim.*)
val insert_before : 'a dblist -> 'a -> 'a -> unit
val insert_after : 'a dblist -> 'a -> 'a -> unit

(*Preciso de conseguir especificar o innerNode*)
val remove_head : 'a dblist -> 'a Node.node
val remove_tail : 'a dblist -> 'a Node.node

val reverse : 'a dblist -> unit
(*@ reverse list
    modifies list
    ensures list.view = List.rev (old list.view) *)

val append : 'a dblist -> 'a dblist -> 'a dblist
(*@ r = append list1 list2
    ensures r.view = (old list1.view) ++ (old list2.view) *)

val josephus : 'a dblist -> int -> unit
(* josephus list k
    modifies list
    requires k > 0
    ensures List.length list.view = 1 *)

val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b dblist -> 'a
(*@ r = fold_left f acc list
    ensures match list.view with
    | [] -> r = acc
    | x::xs -> r = List.fold_left f acc (x::xs) *)

val fold_right : ('a -> 'b -> 'b) -> 'a dblist -> 'b -> 'b
(*@ r = fold_right f list acc
    ensures match list.view with
    | [] -> r = acc
    | x::xs -> r = List.fold_right f (x::xs) acc *)

val iter_left : ('a -> 'b) -> 'a dblist -> 'b
(*@ iter_left f list
    modifies list
    ensures List.for_all (fun x -> f x = ()) list.view *)

val iter_right : ('a -> 'b) -> 'a dblist -> 'b
(*@ iter_right f list
    modifies list
    ensures List.for_all (fun x -> f x = ()) list.view *)
