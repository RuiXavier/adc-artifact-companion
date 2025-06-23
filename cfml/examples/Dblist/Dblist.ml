type 'a node = {
  data : 'a;
  mutable prev : 'a node;
  mutable next : 'a node;
}

let create_node data = let rec new_node = { data; next = new_node; prev = new_node } in new_node

let node_insert_before (new_node : 'a node) (ref_node : 'a node) : unit =
  ref_node.prev.next <- new_node;
  new_node.prev <- ref_node.prev;
  new_node.next <- ref_node;
  ref_node.prev <- new_node

let node_insert_after (new_node : 'a node) (ref_node : 'a node) : unit =
  ref_node.next.prev <- new_node;
  new_node.next <- ref_node.next;
  new_node.prev <- ref_node;
  ref_node.next <- new_node


let remove node =
  let prev = node.prev in
  let next = node.next in
  prev.next <- next;
  next.prev <- prev

let reverse node =
  let prev = node.prev in
  let next = node.next in
  node.prev <- next;
  node.next <- prev

let advance node step =
  let rec advance_helper node step =
    if step = 0 then node
    else advance_helper (node.next) (step - 1)
  in
  advance_helper node step

type 'a innerNode =
  | Nil
  | Cons of 'a node

(* A node in the doubly-linked list *)

(* A doubly-linked list keeps track of its head, tail, and length *)
type 'a dblist = {
  mutable head : 'a innerNode;
  mutable tail : 'a innerNode;
  mutable length : int;
}


(* Create an empty list *)
let create () = {
  head = Nil;
  tail = Nil;
  length = 0;
}

(* Check if the list is empty *)
let is_empty db =
  db.length = 0

let clear db =
  db.head <- Nil;
  db.tail <- Nil;
  db.length <- 0

let get_head_opt db =
  match db.head with
  | Nil -> None
  | Cons h -> Some h

exception Empty
let get_head db =
  match db.head with
  | Nil -> raise Empty
  | Cons h -> h

(* Get the data at the tail node, if it exists *)

let get_tail_opt db =
  match db.tail with
  | Nil -> None
  | Cons t -> Some t

let get_tail db =
  match db.tail with
  | Nil -> raise Empty
  | Cons t -> t

(* Get the data at the tail node, if it exists *)

(* Return the current size of the list *)
let get_size db =
  db.length


(* Insert a new node with data at the front of the list *)
let insert_front db data =
  let new_node = create_node data in
  match db.head with
  | Nil ->
    (db.head <- Cons new_node;
    db.tail <- db.head;
    db.length <- db.length + 1)
  | Cons h ->
    (node_insert_before new_node h;
    db.length <- db.length + 1;
    db.head <- Cons new_node)

(* Insert a new node with data at the back of the list *)
let insert_back db data =
  let new_node = create_node data in
  match db.tail with
  | Nil ->
    db.head <- Cons new_node;
    db.tail <- Cons new_node;
    db.length <- db.length + 1
  | Cons h ->
    node_insert_after new_node h;
    db.length <- db.length + 1;
    db.tail <- Cons new_node

        (*

let insert_before (db: 'a dblist) value new_data =
    let rec insert_before_helper (current: 'a node) value new_data =
      if current.data = value then
        node_insert_before (create_node new_data) current
      else if current.next == (get_head db) then
        raise Not_found
      else
        insert_before_helper current.next value new_data
    in
    match db.head with
    | Nil -> raise Empty
    | Cons h -> insert_before_helper h value new_data


let insert_after db value new_data =
  let rec insert_after_helper current value new_data =
    if current.data = value then
      node_insert_after (create_node new_data) current
    else if current.next == (get_head db) then
      raise Not_found
    else
      insert_after_helper (current.next) value new_data
  in
  match db.head with
  | Nil -> raise Empty
  | Cons h -> insert_after_helper h value new_data

(* Remove the head node and return its data, if possible *)


let remove_head db =
  match db.head with
  | Nil -> raise Empty
  | Cons h ->
    remove h;
    db.length <- db.length - 1;
    if db.length = 0 then
      begin
        db.head <- Nil;
        db.tail <- Nil
      end
    else db.head <- Cons h.next;
    h

(* Remove the tail node and return its data, if possible *)
let remove_tail db =
  match db.tail with
  | Nil -> raise Empty
  | Cons t ->
    remove t;
    db.length <- db.length - 1;
    if db.length = 0 then
      begin
        db.head <- Nil;
        db.tail <- Nil
      end
    else db.tail <- Cons t.prev;
    t

(* Reverse the list by swapping prev and next for each node *)
let reverse db =
  let rec reverse_helper current i =
    if i = db.length then ()
    else begin
      let next = current.next in
      reverse current;
      reverse_helper (next) (i + 1)
    end
  in
  match db.head with
  | Nil -> raise Empty
  | Cons h -> reverse_helper h 0;
  let head = db.head in
  let tail = db.tail in
  db.head <- tail;
  db.tail <- head

(* Append one list to another and return the combined list *)
let append l1 l2 =
  match l1.head, l2.head with
  | Nil, _ -> l2
  | _, Nil -> l1
  | Cons h1, Cons h2 ->
    node_insert_after h2 (get_tail l1);
    l1.tail <- l2.tail;
    l1.length <- l1.length + l2.length;
    l1

let josephus (list: 'a dblist) step =
  let rec josephus_helper current step =
    if list.length != 1 then
      begin
      let node = (advance current step) in
      let head = get_head list in
      let tail = get_tail list in
      if node == head then
        begin
          let _ = remove_head list in
          josephus_helper (get_head list) step
        end
      else if node == tail then
        begin
        let _ = remove_tail list in
        josephus_helper (get_head list) step
        end
      else
        begin
        remove node;
        list.length <- list.length - 1;
        josephus_helper node step
        end
      end
  in
  josephus_helper (get_head list) step



(* Fold functions for the doubly-linked list *)

*)
let fold_left f acc db =
  let rec fold f acc node =
    if node == (get_tail db) then (f acc node.data)
    else fold f (f acc node.data) node.next
  in
  fold f acc (get_head db)

let fold_right f db acc  =
  let rec fold f acc node =
    if node == (get_head db) then (f node.data acc)
    else fold f (f node.data acc) node.prev
  in
  fold f acc (get_tail db)

let rec iter_left_aux f node tail =
  f node.data;
  if not (tail == node) then
    iter_left_aux f node.next tail

let iter_left f db =
  match db.head with
  | Nil -> ()
  | Cons n ->
    match db.tail with
    | Nil -> assert false
    | Cons tail -> iter_left_aux f n tail

let iter_right f db =
  let rec iter_right_aux f node =
    if node == (get_head db) then f node.data
    else begin
      f node.data;
      iter_right_aux f node.prev
    end
  in iter_right_aux f (get_tail db)



(*
(* Test the doubly-linked list *)
let () =
  let list = create () in
  insert_front list 1;
  insert_front list 2;
  insert_front list 3;
  insert_front list 4;
  insert_front list 5;
  insert_front list 6;
  insert_front list 7;
  insert_front list 8;
  insert_front list 9;
  insert_front list 10;
  insert_back list 0;
  Printf.printf("Head: %d\n") (get_head list).data;
  Printf.printf("Tail: %d\n") (get_tail list).data;
  Printf.printf "Original list: \n";
  print_list list;
  reverse list;
  Printf.printf "Reversed list: \n";
  print_list list;
  Printf.printf("Head: %d\n") (get_head list).data;
  Printf.printf("Tail: %d\n") (get_tail list).data;
  josephus list 2;
  Printf.printf "Josephus list: \n";
  print_list list;
  Printf.printf("Head: %d \n") (get_head list).data;





  let print_list list =
  let rec print_helper node =
    if node == (get_tail list) then
      Printf.printf "%d\n" node.data
    else begin
      Printf.printf "%d -> " node.data;
      print_helper node.next
    end
  in
  match list.head with
  | Nil -> Printf.printf "List is empty\n"
  | Cons h -> print_helper h



  *)
