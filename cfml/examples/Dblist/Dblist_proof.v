Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From EXAMPLES Require Import Dblist_ml.
From TLC Require Import LibListZ.

Definition Node A `{EA: Enc A} (v: A) (n p c: loc) : hprop :=
  c ~~~> `{ data' := v; next' := n; prev' := p }.

Lemma Node_open_close : forall A {EA: Enc A} (c: loc) (v: A) (n p: loc),
  c ~> Node v n p
= c ~~~> `{ data' := v; next' := n; prev' := p }.
Proof using. auto. Qed.

Lemma Node_affine : forall A {EA: Enc A} (c: loc) (v: A) (n p: loc),
  haffine (c ~> Node v n p).
Proof using. intros. xunfold Node. xaffine. Qed.

(** A segment of a doubly-linked list. *)
(* Arguments:
   - [from]: Entry pointer address in the forward segment (owned).
   - [to]: Last pointer address in the forward segment (not-owned).
           This is actually the address stored in the [next] field of
           the [last] pointer.
   - [last]: Entry pointer address in the backward segment (owned).
   - [first]: Last pointer address in the backward segment (not-owned).
              This is actually the address stored in the [prev] field of
              the [from] pointer.
*)
Fixpoint NodeSeg A `{EA: Enc A} (L: list A) (to last first from: loc) : hprop :=
  match L with
  | nil => \[to = from] \* \[last = first]
  | x :: L' =>
      \exists (n: loc), (from ~> Node x n first) \* (n ~> NodeSeg L' to last from)
  end.

Lemma NodeSeg_if : forall A {EA: Enc A} (from: loc) (L: list A) (to last first: loc),
  from ~> NodeSeg L to last first =
    If from = to then \[L = nil]
    else \exists x L', \[L = x :: L'].
Admitted.

Lemma NodeSeg_if2 : forall A {EA: Enc A} (from: loc) (L: list A) (to last first: loc),
  from ~> NodeSeg L to last first =
    If last = first then \[L = nil] \* from ~> NodeSeg (@nil A) to last first
    else \exists x L', \[L = x :: L'] \* from ~> NodeSeg (x::L') to last first.
Admitted.

Lemma NodeSegBackward :
  forall A {EA: Enc A} (from: loc) (v: A) (L: list A) (to last first: loc),
    from ~> NodeSeg (L&v) to last first
 ==> \exists (p: loc),
   from ~> NodeSeg L last p first \* last ~> Node v to p.
Admitted.

Fixpoint NodeSeg_backward
  A `{EA: Enc A} (L: list A) (to first from last: loc) : hprop :=
  match L with
  | nil => \[to = from] \* \[last = first]
  | x :: L' =>
      \exists (p: loc),
          (last ~> Node x to p) \*
          (p ~> NodeSeg_backward L' last first from)
  end.

(* Lemma NodeSeg_open_close : *)
(*   forall A {EA: Enc A} (c: loc) (v: A) (L: list A) (to last first n from: loc), *)
(*   (from ~> Node v n first) \* (n ~> NodeSeg L to last from) *)
(* = from ~> NodeSeg (v::L) to last first. *)
(* Proof using. *)
(*   intros. *)
(*   xsimpl* *)

Lemma NodeSeg_cons :
  forall A {EA: Enc A} (from: loc) (v: A) (L: list A) (to last first: loc),
    from ~> NodeSeg (v::L) to last first
  = \exists (n: loc), (from ~> Node v n first) \* (n ~> NodeSeg L to last from).
Proof using. eauto. Qed.

Lemma NodeSeg_nil : forall A (EA: Enc A) (from to last first: loc),
  from ~> NodeSeg (@nil A) to last first
= \[to = from] \* \[last = first].
Proof using. auto. Qed.

Lemma NodeSeg_of_Node : forall A (EA: Enc A) (v: A) (c: loc),
   c ~> Node v c c
==> c ~> NodeSeg (v::nil) c c c.
Proof using.
  intros A EA v c.
  rewrite NodeSeg_cons.
  xsimpl. rewrite NodeSeg_nil.
  xsimpl*.
Qed.

Lemma node_of_NodeSeg : forall A (EA: Enc A) (v: A) (c: loc),
   c ~> NodeSeg (v::nil) c c c
==> c ~> Node v c c.
Proof using.
  intros. xchange NodeSeg_cons ;=> n. xchanges* NodeSeg_nil.
Qed.

Lemma NodeSeg_affine : forall A {EA: Enc A} (from: loc) (L: list A) (to last first: loc),
  haffine (from ~> NodeSeg L to last first).
Proof using.
  intros. gen from to last first. induction L as [| x L']; intros.
  { xunfold NodeSeg. xaffine. }
  { xunfold NodeSeg. xaffine.
    applys Node_affine. }
Qed.

Lemma NodeSeg_forward_backward:
  forall A {EA: Enc A} (x: A) (L: list A) (to last first from: loc),
  from ~> NodeSeg (x :: L) to last first
= last ~> NodeSeg_backward (rev L & x) to first from.
Proof using.
  intros A EA L.
  (* induction_wf IH : list_sub L. destruct L as [| x L']; intros. *)
  (* { rew_list. xunfold NodeSeg. xunfold NodeSeg_backward. xsimpl*. } *)
  (* { admit. } *)
Admitted.


Definition InnerNode A `{EA: Enc A} (L: list A) (p: innerNode_ A) : hprop :=
  match L with
  | nil => \[p = Nil]
  | _ => \exists (c q: loc), \[p = Cons c] \* c ~> NodeSeg L c q q
  end.

Lemma InnerNode_Nil : forall A (EA: Enc A) L,
  Nil ~> InnerNode L
= \[L = (@nil A)].
Proof using.
  intros A EA L.
  xunfold* InnerNode. destruct L as [| x L'].
  { xsimpl*. }
  { xpull*. }
Qed.

Lemma InnerNode_nil : forall A (EA: Enc A),
  Nil ~> InnerNode (@nil A) = \[].
Proof using. intros A EA. xunfolds* InnerNode. Qed.

Lemma InnerNode_cons : forall A (EA: Enc A) (v: A) (L: list A) (p: innerNode_ A),
  p ~> InnerNode (v::L)
= \exists (c q: loc), \[p = Cons c] \* c ~> NodeSeg (v::L) c q q.
Proof using. intros A EA v L p. auto. Qed.

Lemma InnerNode_of_NodeSeg : forall A (EA: Enc A) (v: A) (L: list A) (c q: loc),
  c ~> NodeSeg (v::L) c q q
==> Cons c ~> InnerNode (v::L).
Proof using. intros. xunfolds* InnerNode. Qed.

Lemma InnerNode_If : forall A (EA: Enc A) L p,
  p ~> InnerNode L =
    If p = Nil then
      \[L = (@nil A)]
    else \exists x L' c q, \[L = x :: L'] \* \[p = Cons c] \* c ~> NodeSeg L c q q.
Proof using.
  intros A EA L p. case_if*.
  { rewrite C. xpull.
    { xchanges* InnerNode_Nil. }
    { intros ->. xchange* <- InnerNode_nil. } }
  { xunfold* InnerNode. destruct L as [| x L'].
    { xpull. }
    { xpull*; xsimpl*. } }
Qed.

Definition Dblist A `{EA: Enc A} (L: list A) (l: loc) : hprop :=
  \exists (p q: innerNode_ A),
      (l ~~~> `{ head' := p; tail' := q; length' := length L })
        (* Mário: maybe I can keep this but move it down *)
        (* \* (p ~> InnerNode L) \* *)
        \*
      (If L = nil then \[p = Nil] \* \[q = Nil]
       else
         \exists x L' h t, \[L = x :: L'] \* \[p = Cons h] \* \[q = Cons t]
                        \* (h ~> NodeSeg L h t t)).

Lemma Dblist_If : forall A {EA: Enc A} (L: list A) (l: loc),
    l ~> Dblist L =
      \exists (p q : innerNode_ A),
          (l ~~~> `{ head' := p; tail' := q; length' := length L }) \*
            (If q = Nil then
               \[L = nil] \* \[p = Nil]
             else \exists x L' h t, \[L = x :: L'] \* \[p = Cons h]
                                 \* \[q = Cons t] \* (h ~> NodeSeg L h t t)).
Admitted.

Lemma Dblist_If_head : forall A (EA: Enc A) (L: list A) (l: loc),
    l ~> Dblist L =
      \exists (p q : innerNode_ A),
          (l ~~~> `{ head' := p; tail' := q; length' := length L }) \*
            (If p = Nil then
               \[L = nil] \* \[q = Nil]
             else \exists x L' h t, \[L = x :: L'] \* \[p = Cons h] \*
                                 \[q = Cons t] \* (h ~> NodeSeg L h t t)).
Admitted.

Lemma Dblist_nil : forall (l: loc) A `{EA: Enc A},
  l ~> Dblist (@nil A) =
  \exists (h t: innerNode_ A),
  (l ~~~> `{ head' := h; tail' := t; length' := 0 }) \* \[h = Nil] \* \[t = Nil].
Admitted.


Section Ops.
  Context A {EA: Enc A}.
  Implicit Types L: list A.
  Implicit Types c: loc.
  Implicit Types t: loc.

  Lemma Triple_create_node: forall (v: A),
      SPEC (create_node v)
        PRE \[]
        POST (fun c => c ~> Node v c c).
  Proof using.
    intros v. xcf. xapp ;=> c. xvals.
  Qed.

  Lemma Triple_create_node_seg: forall (v: A),
      SPEC (create_node v)
        PRE \[]
        POST (fun c => c ~> NodeSeg (v::nil) c c c).
  Proof using.
    intros v. xcf.
    xapp ;=> c. xvals*.
    xchanges* <- Node_open_close.
    xchanges* NodeSeg_of_Node.
  Qed.

  Lemma Triple_create :
    SPEC (create tt)
      PRE \[]
      POST (fun t => t ~> Dblist (@nil A)).
  Proof using.
    xcf. xapp* ;=> t. xunfolds* Dblist.
    case_if. xsimpl*.
    (* xunfold InnerNode; xsimpl*. *)
    (* case_if. xsimpl. auto. auto. *)
  Qed.

  Lemma Triple_insert_after_node:
    forall (L: list A) (x: A) (c n: loc) (to last first: loc),
      SPEC (node_insert_after c n)
        PRE (n ~> Node x n n \* c ~> NodeSeg L to last first)
        POSTUNIT (n ~> NodeSeg L to last c ).
Proof using. intros. xcf. Admitted.


  Lemma Triple_push_end : forall L (v: A) t,
      SPEC (insert_back t v)
        PRE (t ~> Dblist L)
        POSTUNIT (t ~> Dblist (L & v)).
  Proof using.
    intros L v t. xcf.
    xchanges* Dblist_If ;=>.
    xapp Triple_create_node ;=> c.
    xapp. case_if; xpull ;=>; xmatch.
    { xapp. xapp. xapp. xapp. subst L.
      xunfold Dblist. case_if. rew_list*.
      xsimpl*.
      (* Mário: the following tactic does [xchange] + [xsimpl].
         [xchanges] = [xchange; xsimpl] *)
      xchanges* NodeSeg_of_Node.
    (* Mário: the above finishes the case of the empty list *)


    (* xunfold Dblist. xpull* ;=> p. intros. *)
    (* xchanges* InnerNode_If. case_if. *)
    (* { xpull* ;=> ->. xapp. xmatch. *)
    (*   xapp. xapp. xapp. xapp. case_if. *)
    (*   xsimpl* ;=>. subst p. *)

    (*   xpull* ;=> ->. xmatch. *)
    (*   xapp. xapp. xapp. xapp. xapp. case_if. *)
    (*   xsimpl*. *)

    (*   xchange NodeSeg_of_Node. rew_list*. *)
    (*   xchanges InnerNode_of_NodeSeg. xapp. xapp. xapp. xsimpl*. *)
    (*   case_if. xsimpl. intros. case_if.  subst p. xchange InnerNode_Nil. intros. *)
    (*   xsimpl.  } *)
    (* { xpull* ;=> x x0 x1 x2 -> ->. xmatch. *)
    (*   xchange* NodeSeg_cons ;=> p. xchange* (node_open_close x1). *)
    (*   xapp. *)

    (*   xchange* NodeSeg_forward_backward. *)
    (*   rew_list. *)


    (*   xunfold NodeSeg_backward. *)
    (*   (* rew_list. *) *)



    (*   xchange* NodeSeg_cons ;=> x3. *)
  Admitted.
    (*   xchange* (node_open_close x1). *)
    (*   xapp. *)
    (*   xchange* <- NodeSeg_cons. *)
    (*   xapp. *)
    (*   xlet. *)
    (*   xunfold* Node. *)
    (*   xchange <- Node_cons. *)

    (* xapp*. xmatch. *)
  (* { xapp. xapp. xsimpl*. *)

  (*
  Assumi que a definição tinha de ter em conta qualquer chamada intermédia

  L' -> visited até agora
  L -> Lista Completa em si
  t -> pointer para a lista
  n -> nó usado pelo iter_left_aux

  L1 -> parte da lista que ainda falta visitar tirando x
  x -> proximo elemento a ser visitado


  Como dizer que x é o valor dentro do nó n?
  Será que é necessária essa relação?
  Como definir um nodeSeg que vai de n até ao fim da lista?
  Preciso de receber como argumento o last first from e to?
  *)
  Lemma Triple_iter_left_aux :
    forall (f: val) (I : list A -> hprop) (L L1 L2: list A) n e h p,
      (forall x L1 L2, L = L1 ++ x :: L2 ->
                  SPEC (f x)
                    PRE (I L1)
                    POSTUNIT (I (L1 & x))) ->
      L = L1 ++ L2 ->
      L2 <> nil ->
      SPEC (iter_left_aux f n e)
        PRE  (n ~> NodeSeg L2 h e p\* I L1)
        POSTUNIT (n ~> NodeSeg L2 h e p \* I L).
  Proof using.
    introv Specf. gen L1 n p.
    induction_wf IH : list_sub L2.
    xcf. destruct L2 as [| x2 L2']; tryfalse.
    xchange NodeSeg_cons ;=>. xchange Node_open_close.
    xunfold NodeSeg at 2.
    xapp. xapp (Specf x2 L1 L2'); eauto.
    xapp. xif; =>.
    { xchange NodeSeg_if2. case_if. xpull*; =>.
      subst L2'; rew_list*. xchange NodeSeg_cons ;=>.
      xapp. xchange <- NodeSeg_cons. xapp; rew_list*; eauto.
      intros false; false.
      xsimpl*. xchanges <- Node_open_close. }
    { xchange NodeSeg_if2. case_if. xpull*; => ->.
      subst. xchanges <- Node_open_close. xvals. }
  Qed.

  Lemma Triple_iter_left : forall (I: list A -> hprop) L (f: val) t,
      (forall x L1 L2, L = L1 ++ x :: L2 ->
        SPEC (f x)
          PRE (I L1)
          POSTUNIT (I (L1 & x))) ->
      SPEC (iter_left f t)
        PRE (t ~> Dblist L \* I nil)
        POSTUNIT (t ~> Dblist L \* I L).
  Proof using.
    introv Specf.
    xcf. xchange* Dblist_If_head ;=>. xapp. case_if; xpull ;=>; xmatch.
    { xval. subst L. subst x0. xsimpl*. xunfold Dblist.
      case_if. xsimpl*. }
    { inversion TEMP; subst.
      xchange NodeSeg_cons ;=> .
      xapp. xmatch.
      xchange <- NodeSeg_cons.
      xapp (@Triple_iter_left_aux f I (x1::x2) nil); rew_list*.
      { intros false; false. }
      xunfolds Dblist; rew_list*. case_if. xsimpl*. }
    Qed.

  Lemma Triple_fold_left_aux :
    forall {B} (f: val) (I : B -> list A -> hprop) (L L1 L2: list A) (acc: B) n e h p,
      (forall acc x L1 L2, L = L1 ++ x :: L2 ->
                  SPEC (f acc x)
                    PRE (I acc L1)
                    POST (fun accu => I accu (L1 & x))) ->
      L = L1 ++ L2 ->
      SPEC (fold_left_aux f acc n e)
        PRE (n ~> NodeSeg L2 h e p \* I acc L1)
        POST (fun accu => n ~> NodeSeg L2 h e p \* I accu L).
  Proof using. Admitted.

  Lemma Triple_fold_left : forall {B} (I: B -> list A -> hprop) L (f: val) t (acc: B),
      (forall acc x L1 L2, L = L1 ++ x :: L2 ->
        SPEC (f acc x)
          PRE (I acc L1)
          POST (fun accu => I accu (L1 & x))) ->
      SPEC (Dblist_ml.fold_left f acc t)
        PRE (t ~> Dblist L \* I acc nil)
        POST (fun accu => t ~> Dblist L \* I accu L).
  Proof using.
    introv Specf. xcf. xchange* Dblist_If_head ;=>.
    xapp. case_if; xpull ;=>; xmatch.
    { xval. subst L. subst x0. xsimpl*. xunfold Dblist.
      case_if. xsimpl*. }
    { inversion TEMP; subst.
      xchange NodeSeg_cons ;=> .
      xapp. xmatch.
      xchange <- NodeSeg_cons.
      xapp (@Triple_fold_left_aux B f I (x1::x2) nil); rew_list*.
      xunfolds Dblist; rew_list*. case_if. xsimpl*.
    }
  Qed.

  Lemma Triple_clear : forall (p: loc) (L: list A) (h t: innerNode_ A),
    SPEC (clear p)
      PRE (p ~~~> `{ head' := h; tail' := t; length' := length L })
      POSTUNIT (p ~> Dblist (@nil A)).
  Proof using.
    intros. xcf. xapp. xapp. xapp. xchanges* <- Dblist_nil.
  Qed.

  Lemma Triple_clear_alt : forall (p: loc) (L: list A) (h t: innerNode_ A),
    SPEC (clear p)
      PRE (p ~> Dblist L)
      POSTUNIT (p ~> Dblist (@nil A)).
  Proof using.
    intros. xcf. xunfold Dblist; xpull ;=>. xapp. case_if; xpull ;=>.
    { xapp. xapp. case_if. xsimpl*. }
    { xapp. xapp. case_if. xsimpl*. applys NodeSeg_affine. }
  Qed.


End Ops.
