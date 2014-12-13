Require Export
 HoTT
 Nat
 generalLists
 nCkEqns.

Fixpoint blobList (A : nat -> Type) (n k: nat) :
  lType k :=
match k with
| O => tt
| S k' => ( nCkList (A k') n k', blobList A n k' ) end.

Definition adhesive (A : nat -> Type) :=
  forall n,
    ( A (S n) * (nCkList (A n) (S n) n) ) -> Type.

Fixpoint gluetype (A : nat -> Type) (adh : adhesive A) {n k : nat}:
  lSect (blobList A n (S k)) -> lType k.
Proof.
  intros.
  destruct k.
    exact tt.
    refine ( _ , gluetype A adh n k (snd X)).
 exact (nCkSect (nCkT_S (
          nCkApply
           (nCkKMap (adh _) _ _)
             (nCkLPair (fst X) (nCkSubdiv _ (fst (snd X))))))).
Defined.

(** 
  gtyp A adh Z . l :: map (adh l) {cx => (Z.S l)cx , { cy=> Z.l.(cy#cx)}}
*)

Fixpoint subdivided_blob_list { A } {n} l {k} :
  forall (Z : lSect (blobList A n k)),
   nCkList ( lSect (blobList A l k) ) n l.
Proof.
  intros.
  destruct k.
  exact (nCkKonst tt _ _ ).
  apply nCkLPair.
    exact (nCkSubdiv l (fst Z)).
    exact (subdivided_blob_list A n l k (snd Z)).
Defined.

(* 
  Z : blobList (A n k)

  ├─

  (sdbl l Z).cx.t = nCkSubdiv l (Z .t). cx
                  = { cy => nCkSubdiv l (Z.t) . (cx#cy) }
or
  (sdbl l Z).cx.t.cy = nCkSubdiv l (Z.t) . (cx#cy)

*)

Fixpoint gluingSubdivided { A } ( adh : adhesive A ) { n } l { k } :
forall ( Z : lSect (blobList A n (S k)) ),
   lList (nCkType n l) k.
Proof.
  intros.
  destruct k.
    exact tt.
    refine ( _ , gluingSubdivided A adh _ _ _ (snd Z)).
    exact
      (listT_of_Sects (
        nCkTSubdiv l ( nCkT_S (
         nCkApply (nCkKMap (adh _) _ _)
          (nCkLPair (fst Z) (nCkSubdiv _ (fst (snd Z)))))))).
Defined.

(*
 (gsd adh m Z).l = 
      (listT_of_Sects (
        nCkTSubdiv m ( nCkT_S (
         nCkApply (nCkKMap (adh l) _ _)
          (nCkLPair (Z.S l) (nCkSubdiv (S l) (Z.l))))))).

   (gsd adh m Z).l.cx =
     Sect ((subdiv m ( nCkT_S ( Map (adh l) (nCkLPair (Z.S l) (subdiv (S l) (Z.l)))))).cx)
   = Sect { cy : 〈n C m〉 => (Map (adh l) (nCkLPair (Z.S l) (subdiv (S l) (Z.l)))).(cy#cx) }
   = ∀ cy , (adh l) ( (Z.S l).(cy#cx), (subdiv (S l) (Z.l)).(cy#cx))
*)

Fixpoint subdividedGlue { A } (adh : adhesive A) { n } l { k } :
  forall { Z : lSect (blobList A n (S k)) }
    ( zg : lSect (gluetype A adh Z) ),
       lSect (nckt_nck_l (gluingSubdivided adh l Z)).
Proof.
  intros.
  destruct k.
    exact tt.
    refine ( _ , subdividedGlue A adh n l k (snd Z) (snd zg)).
    destruct zg as [ glue1 zg' ].
    simpl.
    exact (nCkSSubdiv l glue1).
Defined.

Definition partitionSubdivided { A } ( adh : adhesive A ) { n } l { k } :
forall ( Z : lSect (blobList A n (S k)) ),
   nCkList (lType k) n l := 
   fun Z =>
   ( nCkApply (nCkKMap (gluetype A adh) _ _) (subdivided_blob_list l Z )).

(** 
  now, this is a monster of a proof script, in terms of length
  (compared to my others, anyways)
  but it really isn't as bad as it looks; the decisions at every stage
  are meant to be the most straight-forward, given how we want to
  simplify either the goal or an hypothesis.
  I should love to see it automated better
  *)

Lemma glue_from_glue  { A } (adh : adhesive A) { n } l { k } :
  forall { Z : lSect (blobList A n (S k)) }
    ( zg : lSect (gluetype A adh Z) ),
  nCkSect (nCkT_S (nCkApply (nCkKMap lSect _ _) (partitionSubdivided adh l Z))).
Proof.
  induction k.
    intros.
    simpl.
    apply nCkAllUnit.
    intros.
    simpl.
    destruct Z as [ Z0 Z ].
    apply sect_ts_forall. intro.
    unfold partitionSubdivided.
     apply lf_comp. simpl.
     apply lf_snd.
      apply lf_fst.
     apply lf_fst.
    destruct zg as [ zg0 zg ].
    split.
     apply (sect_ts_forall (adh k)).
     intro.
     apply listFun_pairs.
    apply subdivHtp.
    assert ( help :=
      let ( _ , hlp ) := sect_ts_forall (adh k) (nCkLPair Z0 (nCkSubdiv _ (fst Z)))
       in hlp zg0 ).
    assert ( help2 := 
     let ( _ , hlp) := 
      listFun_pairs (adh k) Z0 (nCkSubdiv _ (fst Z)) (nCkComp cx cx0) in
        hlp (help _)).
    refine (transport (fun z => 
      adh k (listFun Z0 (nCkComp cx cx0), z)) _ help2).
    apply listEqn.
    intro cz.
    apply subdivHtp.
    apply subdivHtp.
    apply subdivHtp.
    apply nCk_assoc. exact idpath.
    apply (lf_comp (gluetype A adh) lSect).
    assert  ( rough := IHk Z zg ).
    refine ( let 
     ( _ , hlp ) :=
      sect_ts_forall lSect (partitionSubdivided adh l Z) in
        hlp rough cx).
Defined.
