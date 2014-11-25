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
    forall n, (adj_Names (S n)) -> (nCkList n (S n) (adj_Names n)) -> Type
  }.

Record Cells (A : Adjacency) (n : nat) :={
  cell_facets : forall k, 
    nCkList k n (adj_Names A k);
  cell_glue : forall k, forall z : nCk n (S k),
    (adj_Rels A) _ (depS_nCkS' (cell_facets (S k)) z)
      (depS_nCkS' (nCkSubdiv (S k) (cell_facets k)) z )
      }.

Definition topFacet (A : Adjacency) (n : nat) (C : Cells A n) : 
  adj_Names A n.
Proof.
  destruct C as [ facets _ ].
  exact ( depS_nCkS' (facets n) nCAll).
Defined.


(*
Definition boundary (A : Adjacency) (n : nat) (C : Cells A (S n)) :
  nCkList n (S n) (Cells A n).
Proof.
  destruct C as [ facets glue ].
  apply nCkS_depS.
  intro.
  assert ( help := fun k => fun z => glue k (nCkCompose x z) ).
  refine ( Build_Cells A n _ help ). *)