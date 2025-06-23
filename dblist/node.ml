type 'a node = {
  data : 'a;
  mutable prev : 'a node;
  mutable next : 'a node;
}

let create data = let rec new_node = { data; prev = new_node; next = new_node } in new_node

let insert_before (new_node : 'a node) (ref_node : 'a node) : unit =
  ref_node.prev.next <- new_node;
  new_node.prev <- ref_node.prev;
  new_node.next <- ref_node;
  ref_node.prev <- new_node

let insert_after (new_node : 'a node) (ref_node : 'a node) : unit =
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