type 'a node = private {
    data: 'a;
    mutable prev: 'a node;
    mutable next: 'a node;
}
(*@ mutable model data: 'a
    mutable model prev: 'a list
    mutable model next: 'a list*)

val create_node : 'a -> 'a node
(*@ r = create_node value
    ensures r.data = value *)

val node_insert_before : 'a node -> 'a node -> unit
(*@ node_insert_before new_node ref_node
    modifies ref_node, new_node
    ensures ref_node.prev = (new_node.data)::(old ref_node.prev)
    /\ new_node.next = (ref_node.data)::(ref_node.next) *)

val node_insert_after : 'a node -> 'a node -> unit
(*@ node_insert_after new_node ref_node
    modifies ref_node, new_node
    ensures ref_node.next = (new_node.data)::(old ref_node.next)
    /\ new_node.prev = (ref_node.data)::(ref_node.prev) *)


val remove : 'a node -> unit
(*Como especificar que o prev.next = next && next.prev = prev,
sendo que agora a minha representação lógica não tem noção de prev.next/next.prev*)

val reverse : 'a node -> unit
(*@ reverse node
    modifies node
    ensures node.prev = (old node.next)
    /\ node.next = (old node.prev) *)

val advance : 'a node -> int -> 'a node
(*Como especificar que esta função pega num node e me
retorna o nó que está "step" nodes à frente*)
