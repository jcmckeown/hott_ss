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

Definition Cells (A : Adjacency) (n : nat) : Type :={
  cell_facets : forall k, 
    nCkList (adj_Names A k) k n &
 forall k, forall z : nCk n (S k),
    (adj_Rels A) _ (fun_list (cell_facets (S k)) z)
      (fun_list (nCkSubdiv (S k) (cell_facets k)) z )
      }.

Definition topFacet (A : Adjacency) (n : nat) (C : Cells A n) : 
  adj_Names A n.
Proof.
  destruct C as [ facets _ ].
  exact ( fun_list (facets n) nCAll).
Defined.

Definition skel { A : Adjacency } (k: nat) { n : nat } (C : Cells A n) :
  nCkList (Cells A k) k n.
Proof.
  destruct C as [ facets glue ].
  apply list_fun.
  intro cx.
  exists ( fun k => (fun_list (nCkSubdiv _ (facets k)) cx) ).
  intros.
  rewrite nCkEqn.
  refine ( transport _ _ (glue _ (nCkCompose cx z))).
  unfold nCkSubdiv.
    repeat progress ( rewrite fl_inv ).
    apply nCkLEqn.
    intro cz.
    repeat progress ( rewrite fl_inv ).
    apply ap.
    symmetry.
    exact (nCkAssoc cx z cz).
Defined.

Definition boundary (A : Adjacency) (n : nat) (C : Cells A (S n)) :=
  skel n C.

Definition SSClosure (A : Adjacency) : Adjacency := 
 Build_Adjacency ( Cells A ) ( fun k => valPath (boundary A k) ).

Definition cellClosure (A : Adjacency) :
  forall n,
    (Cells A n) -> (Cells (SSClosure A) n).
Proof.
  intros n C.
  exists ( fun k => skel k C).
  simpl.
  intros k [ l [ cx y ]].
  unfold valPath.
  unfold boundary.
  unfold nCkSubdiv.
  simpl. rewrite depS_inv.
  rewrite fl_inv. simpl.
  apply nCkLEqn.
    intro.
    rewrite fl_inv.
  destruct A as [ Fs Gs ].
  unfold adj_Rels. unfold adj_Names.
  admit. (** There is a proof, hinging on nCkAssoc and dec_eq_nCk,
   and a machine could write it;
   so, someone, start building Ltacs for eliminating thin homotopy *)
Qed.

(** We don't need cellClosure to define these; it's more why these are correct (eventually) *)

Record mapsComplex :=
 { mc_names : nat -> Type ;
   mc_maps : forall n, mc_names (S n) -> nCkList (mc_names n) n (S n)
   }.

Definition maps_adj (M : mapsComplex) : Adjacency :=
  Build_Adjacency (mc_names M) (fun k => valPath (mc_maps M k)).

(** This promotes a mapsComplex to a coloured simplicial set *)
Definition IsCSimplicialSet (M : mapsComplex) :=
  forall n, IsEquiv ( topFacet (maps_adj M) n).

(** an ordinary semisimplicial set... *)
Record SimplicialSet := {
  SS_M : mapsComplex;
  SS_Simpl : IsCSimplicialSet SS_M;
  SS_Contr : Contr (mc_names SS_M 0)
}.
