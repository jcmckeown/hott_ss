Require Import
 HoTT
 Nat
 austere_nCk
 lList
 FunctionRels.

Record Adjacency : Type := {
  adj_Names : nat -> Type;
  adj_Rels : 
    forall n, ((adj_Names (S n)) * (nCkList (adj_Names n) (S n) n)) -> Type
  }.

Section test.

  Hypotheses Ad : Adjacency.
  Hypotheses (n : nat)
     ( facets : lSect (lT_fun (fun k : LT (S n) => nCkList (adj_Names Ad (k.1)) n (k.1) )) ).
  
  Hypotheses k : LT n.
  
  Definition glueType : Type :=
   let ( k' , ord ) := k in
    nCkSect (nCkT_S (nCkApply (nCkKMap (adj_Rels Ad _) _ _)
       (nCkLPair (fun_lS _ facets (S k';  ord))
                 (nCkRSubdivide (S k') (fun_lS _ facets (k' ; lt_trans (lt_S _ ) ord )))))).

End test.

Definition Cells (A : Adjacency) (n : nat) := {
  cell_facets : lSect (lT_fun (fun k : LT (S n) => nCkList (adj_Names A k.1) n k.1 )) &
   lSect (lT_fun 
    (glueType A n cell_facets) ) }.

Definition topFacet (A : Adjacency) (n : nat) (C : Cells A n) : 
  adj_Names A n.
Proof.
  destruct C as [ facets _ ].
  exact ( nCTop (fun_lS _ facets ( n ; lt_S n ) ) ).
Defined.

Fixpoint boundary (A : Adjacency) (n : nat) (C : Cells A (S n)) :
  nCkList (Cells A n) (S n) n.
Proof.
  destruct C as [ facets glue ].
  destruct n.
    exists ( (fun_lS _ facets ( 0 ; tt )) , tt ).
    exact tt.
  split.
Abort.

(*   perhaps we really want subdivision of dependently-typed things? 
~~~~~
  apply nCkS_depS.
  intro.
  assert ( help := fun k => fun z => glue k (nCkCompose x z) ).
  refine ( Build_Cells A n _ help ).
~~~~~
   *)