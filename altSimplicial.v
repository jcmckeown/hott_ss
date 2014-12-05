Require Import
 HoTT
 Nat
 generalLists
 FunctionRels.

(* this one really belongs in nCk.v ... *)

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

Fixpoint subdivided_blob_list { A } (adh : adhesive A) {n} l {k} :
  forall (Z : lSect (blobList A n k)),
   nCkList ( lSect (blobList A l k) ) n l.
Proof.
  intros.
  destruct k.
  exact (nCkKonst tt _ _ ).
  apply nCkLPair.
    exact (nCkSubdiv l (fst Z)).
    exact (subdivided_blob_list A adh n l k (snd Z)).
Defined.

(** oh, is this where we need associativity? that'd be irksome... *)

(*
Fixpoint repackage {A} {adh : adhesive A} {n} l {k} :
  forall { Z : lSect (blobList A n (S k)) }
   (rough_ans : nCkSect (lt_l_nck (l_nck_nck_l (gluingSubdivided adh l Z)))),
    nCkSect (nCkT_S 
      (nCkApply (nCkKMap (fun z => lSect (gluetype A adh z)) _ _)
                        (subdivided_blob_list adh l Z))).
Proof.
  intros.
  destruct k.
    apply nCkAllUnit.
    simpl.
    destruct Z as [ Z1 [ Z2 zs ]].
    apply nCkMPair.
    simpl.
    unfold lt_l_nck, l_nck_nck_l in rough_ans.
    
    simpl in rough_ans.
     unfold 
    assert ( helper := nCkfst rough_ans ).


Lemma ncklist_of_gluings { A } (adh : adhesive A) { n } l { k } :
  forall { Z : lSect (blobList A n (S k)) }
    (zg : lSect (gluetype A adh Z)),
    nCkSect 
     (nCkT_S
      (nCkApply
       (nCkKMap (fun z => lSect (gluetype A adh z)) _ _)
                (subdivided_blob_list adh l Z))).
Proof.
  intros.
  assert ( rough_ans := nckls_lncks _ (subdividedGlue adh l zg)).

   (** The rough idea from here is that
    the *)
  unfold l_nck_nck_l, lt_l_nck in rough_ans. simpl in *.
  clear zg.
  revert n l Z rough_ans.
  induction k.
   intros.
   simpl.
   destruct n.
    destruct l.
     exact tt.
     exact tt.
    destruct l.
     exact tt.
     split; simpl.
     apply nCkAllUnit.
     apply nCkAllUnit.
   intros.
   simpl.
   destruct n.
    destruct l.
     destruct k. 
     simpl in *.
*)