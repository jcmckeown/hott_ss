Require Import
 FunctionRels
 adhesives.

Record Adjacency : Type := {
  adj_Names : nat -> Type;
  adj_Rels : adhesive adj_Names
  }.


Definition frame (A : Adjacency) (n k : nat) :=
  { 
    facets : lSect (blobList (adj_Names A) n (S k))
      & 
      lSect (gluetype _ (adj_Rels A) facets) }.

Definition Cell (A : Adjacency) (n : nat) :=
  frame A n n.

Definition topFacet (A : Adjacency) (n : nat) (C : Cell A n) : 
  adj_Names A n := nCTop (fst (C .1)).

Lemma fskel { A : Adjacency } n k l :
  forall (C : frame A n k),
    nCkList (frame A l k) n l.
Proof.
  intros.
  refine 
    (nCkLExistT (subdivided_blob_list l (C.1)) _).
  assert ( ans := glue_from_glue _ l C.2 ).
  unfold partitionSubdivided in ans.
  apply sect_ts_forall.
  intro.
  assert ( help :=
    let ( _ , hlp ) :=
      sect_ts_forall lSect 
        (nCkApply _ _) in hlp ans cx).
  apply lf_comp. auto.
Defined.

Fixpoint bottomLayer (A : Adjacency) { n k : nat } :
  frame A n k -> frame A n 0.
Proof.
  destruct k.
    intro. exact X.
(*  intros [ [ a fs ] [ _ gs]].
    simpl in gs. clear a. *)
  intro X.
  exact (bottomLayer _ _ _ 
    (snd X.1; snd X.2)).
Defined.

Fixpoint excessFrame (A : Adjacency) { n k : nat } :
  frame A n k -> (lt (S k) n) -> Cell A n.
Proof.
  destruct k.
    destruct n.
    intros. exact X.
    contradiction.
  intros.
    destruct n.
      refine (bottomLayer _ X).
    destruct (opt_ltS X0).
      destruct p.
      exact X.
(*    destruct X as 
      [ [ a fs ] [ b gs ]]. *)
    exact (excessFrame A (S n) k (snd X.1 ; snd X.2) l).
Defined.

Lemma cellFaces (A : Adjacency) (n k : nat) :
  Cell A n -> nCkList (Cell A k) n k.
Proof.
  intro.
  assert (help := fskel _ _ k X).
  assert (evenBetter := nCkLPair help (nCk_lt _ _)).
  refine (nCkApply (nCkKMap _ _ _ ) evenBetter ).
  intro. (* intros [ fm ord ]. *)
  exact (excessFrame _ (fst X0) (snd X0)).
Defined.

Definition boundary (A : Adjacency) (n : nat) := (cellFaces A (S n) n).

Record MapsComplex := { 
  mc_spaces : nat -> Type;
  mc_maps : forall n,
    mc_spaces (S n) -> nCkList (mc_spaces n) (S n) n
}.

Definition mapRels :
  MapsComplex -> Adjacency :=
 fun M =>
  {| adj_Names := mc_spaces M ; 
     adj_Rels := fun n => 
      fun z => valPath (mc_maps M n) (fst z) (snd z) |}.

Definition relMaps :
  Adjacency -> MapsComplex :=
 fun Adj =>
  {| mc_spaces := Cell Adj ;
    mc_maps := boundary Adj |}.

Fixpoint frameList (A : Adjacency) (n k : nat):
  Cell A n ->
    lSect (blobList (adj_Names (mapRels (relMaps A))) n k).
Proof.
  intros.
  destruct k.
    exact tt.
    split.
    simpl.
    exact (cellFaces A n k X).
    exact (frameList A n k X).
Defined.

Lemma cellClosure (A : Adjacency) (n k : nat) :
  Cell A n -> frame (mapRels (relMaps A)) n k.
Proof.
  intro.
  exists (frameList A n (S k) X).
  induction k.
    exact tt.
  simpl.
    unfold valPath.
    split; try apply IHk.
    clear.
    apply sect_ts_forall.
    intro.
    apply lf_fst.
    apply lf_snd.
    apply listEqn.
    intro cy.
    apply subdivHtp.
    unfold boundary.
    revert cx cy.
    generalize (S k) as l.
    intros. (** this really should be obvious by now... *)
  admit.
Defined.

(*
 
 Check cellClosure_admitted
 
 *)

(** some things one can try ... 

(*
  unfold cellFaces.
  intros.
  apply lf_comp. apply lf_snd.
  apply lf_fst.
  apply lf_comp.
  apply lf_fst.
  apply lf_snd.
  apply lf_comp.
  apply lf_fst. apply lf_snd. *)
  
  revert k X l cx cy.
  induction n.
    intros.
    destruct l; try contradiction.
    destruct k; try contradiction.
    auto.
    destruct l.
      destruct k; try contradiction.
      intros.
      simpl.
      unfold cellFaces at 2.
      simpl.
      unfold fskel. simpl.
        destruct (cellFaces A (S n) 0 X). destruct l.
          destruct x. destruct l. auto.
    intros.
    destruct cx as [ lx | rx ].
     destruct k.
      destruct cy. simpl nCkComp. lazy beta iota.
    apply lf_comp.
    clear.
    revert cx cy. clear.    

*)    

Definition cellCompletion (A : Adjacency) (n : nat) :
  Cell A n -> Cell (mapRels (relMaps A)) n :=
    cellClosure A n n.

Lemma cellTopCell (A : Adjacency) (n : nat) :
forall C : Cell A n,
  topFacet _ _ (cellCompletion A n C) = C.
Proof.
  admit.
  (* Just for fun, kill the "admit" there and run these
   instead :
  induction n.
  intro.
  
  unfold cellCompletion.
  destruct C. destruct l.
  destruct x. destruct l. exact idpath.
    destruct n.
      intro.
      destruct C.
        destruct x.
          destruct l0.
          destruct l0.
          destruct l.
          destruct l.
          destruct n.
          simpl in n, n2.
          destruct n2.
          cbv in n0.
          destruct A.
          destruct n1.
          destruct n2.
          cbv in n1.
          simpl in n.
          exact idpath.
    destruct n.
     intro.
     destruct C.
      destruct x as [ x2 [ x1 [ x0 [] ] ]].
      destruct x2 as [ [ x2 [] ] [ [] [] ] ].
      simpl in x2.
      destruct x1 as [ x1a [ x1b []]] .
        simpl in x1a, x1b.
    change (adj_Names A 0) in x0.
     destruct l as [ l1 [ l0 []]].
     simpl in l1.
     simpl in l0.
    destruct l1 as [ [ w [] ] [ [] []]].
    destruct l0 as [ wa [ wb [] ] ].
    exact idpath.
    (** etc. *)
    *)
Qed.

(** This promotes a mapsComplex to a coloured simplicial set *)

Definition IsCSimplicialSet (M : MapsComplex) :=
forall n, IsEquiv (topFacet (mapRels M) n).

(** an ordinary semisimplicial set... *)
Record SimplicialSet := {
  SS_M : MapsComplex;
  SS_Simpl : IsCSimplicialSet SS_M;
  SS_Contr : Contr (mc_spaces SS_M 0)
}.

Definition ifZElse { A : Type } (zcase : A ) ( seq : nat -> A ) :
 nat -> A :=
fun z => match z with
| O => zcase
| S n => seq (S n) end.

Definition pushMaps ( M : MapsComplex ) ( X : Type )
  (f : mc_spaces M 0 -> X) :
  MapsComplex.
Proof.
  exists ( ifZElse X (mc_spaces M)).
  intros.
  destruct n; simpl in *.
  apply f.
  apply (mc_maps M 0).
  auto.
  apply (mc_maps M (S n)).
  auto.
Defined.

Lemma pushFrames (M : MapsComplex) (X : Type) 
  (f : mc_spaces M 0 -> X)(n k : nat) :
  frame (mapRels M) n k -> frame (mapRels (pushMaps M X f)) n k.
Proof.
  intros [ fs gs ].
  induction k.
  simpl in *.
   destruct n;
    exists ( f (fst fs) , tt ); exact tt.
  

Lemma push_simplicial (M : MapsComplex) (X : Type) 
  (f : mc_spaces M 0 -> X ) ( H : IsCSimplicialSet M ) :
    IsCSimplicialSet (pushForward M X f).
Proof.
  intro.
  destruct n.
    unfold topFacet.
    unfold nCTop.
    unfold mapRels.
    unfold Cell.
    unfold frame.
    simpl.
      apply isequiv_adjointify with
        (fun x => existT (fun _ => Unit) ( x , tt ) tt ).
      intro. auto. intro. destruct x. destruct u. destruct x.
      destruct u. auto.
    