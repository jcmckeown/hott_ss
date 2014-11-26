Require Import
 HoTT
 Nat
 nCk
 ordmap
 nCkList
 FunctionRels.

Record Adjacency : Type := {
  adj_Names : nat -> Type;
  adj_Rels : 
    forall n, (adj_Names (S n)) -> (nCkList (adj_Names n) n (S n)) -> Type
  }.

Record Cells (A : Adjacency) (n : nat) :={
  cell_facets : forall k, 
    nCkList (adj_Names A k) k n;
  cell_glue : forall k, forall z : nCk n (S k),
    (adj_Rels A) _ (fun_list (cell_facets (S k)) z)
      (fun_list (nCkSubdiv (S k) (cell_facets k)) z )
      }.

Definition topFacet (A : Adjacency) (n : nat) (C : Cells A n) : 
  adj_Names A n.
Proof.
  destruct C as [ facets _ ].
  exact ( fun_list (facets n) nCAll).
Defined.

Definition boundary (A : Adjacency) (n : nat) (C : Cells A (S n)) :
  nCkList (Cells A n) n (S n).
Proof.
  destruct C as [ facets glue ].
  apply list_fun.
  intro cx.
  exists ( fun k => (fun_list (nCkSubdiv n (facets k)) cx) ).
  intros.
  rewrite nCkEqn.
  assert ( help := fun k => fun cz => glue k (nCkCompose cx cz) ).
  refine ( transport _ _ (help _ z)).
  unfold nCkSubdiv.
    repeat progress ( rewrite fl_inv ).
    apply nCkLEqn.
    intro cz.
    repeat progress ( rewrite fl_inv ).
    apply ap.
    symmetry.
    apply nCkAssoc.
Defined.