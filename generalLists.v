Require Import
  HoTT
  Nat.
Require Export
  lList
  austere_nCk.

Fixpoint nCk_lt (n k : nat) : nCkList (lt (S n) k) n k.
Proof.
  destruct n.
    destruct k.
      exact tt.
      exact tt.
    destruct k.
      exact tt.
    split.
      change (nCkList (lt (S n) k) n k). apply nCk_lt.
      change (nCkList (lt (S n) k) n (S k)).
      refine (nCkApply (nCkKMap _ _ _) (nCk_lt n (S k))).
      intro.
      refine (lt_trans (lt_S _) X).
Defined.

Fixpoint l_nck_nck_l { k l m : nat } :
  lList (nCkType k l) m -> nCkList (lType m) k l.
Proof.
  destruct k.
    destruct l.
      exact lT_S.
    intros. exact tt.
    destruct l.
      exact lT_S.
    intros.
    exact 
      ( l_nck_nck_l _ _ _ (l_Lfst X),
        l_nck_nck_l _ _ _ (l_Lsnd X) ).
Defined.

Fixpoint ln_nl_alt { k l m : nat } :
  lList (nCkType k l) m -> nCkList (lType m) k l.
Proof.
  intros.
  destruct m.
    exact (nCkKonst tt _ _).
    exact (nCkLPair (fst X) (ln_nl_alt _ _ _ (snd X))).
Defined.

Fixpoint nck_l_l_nck { k l m : nat } :
  nCkList (lType m) k l -> lList (nCkType k l) m.
Proof.
  destruct k.
    destruct l.
    apply lS_T.
    intro. apply lKonst.
      exact tt.
    intro L.
    destruct l.
    exact (lS_T L).
    destruct L as [ Lkl LkSl ].
    refine ( l_LPair (nck_l_l_nck _ _ _ Lkl)
             (nck_l_l_nck _ _ _ LkSl)).
Defined.

Fixpoint nckt_nck_l { k l m : nat } :
  lList (nCkType k l) m -> lType m :=
match m with
  | O => fun _ => tt
  | S m' => fun LcxL =>
    ( nCkSect (fst LcxL) , nckt_nck_l (snd LcxL) ) end.

Fixpoint lt_l_nck { k l m : nat } :
  nCkList (lType m) k l -> nCkType k l :=
match k return nCkList (lType m) k l -> nCkType k l with
  | O => 
    match l with
      | O => fun X : lType m => lSect X 
      | S l' => fun _ => tt end
  | S k' =>
    match l with
      | O => fun X : lType m => lSect X 
      | S l' => fun X =>
        ( lt_l_nck (fst X) , lt_l_nck (snd X)) end end.

Fixpoint lt_l_nck_alt { k l m : nat } :
 nCkList (lType m) k l -> nCkType k l :=
match m with
  | O => fun _ => nCkLT Unit k l
  | S m' =>
    fun ( w : nCkList (Type * lType m') k l) =>
      nCkProd (nCkT_S (nCkLfst w)) (lt_l_nck_alt (nCkLsnd w)) end.

Fixpoint noneOfAnything { l m } :
    forall (LNCK : lList ( nCkType l m ) 0),
      nCkSect ( lt_l_nck ( l_nck_nck_l LNCK )).
Proof.
  intros.
  destruct l.
    destruct m. 
      exact tt.
      exact tt.
    destruct m.
      exact tt.
      split.
      refine ( noneOfAnything l m _ ).
      refine ( noneOfAnything l (S m) _).
Defined.

Fixpoint nckls_step { k l m : nat } :
  forall t1 : nCkType k l,
   forall lnck : lList (nCkType k l) m,
    nCkSect t1 -> nCkSect (lt_l_nck (l_nck_nck_l lnck)) ->
      nCkSect (lt_l_nck (@l_nck_nck_l _ _ (S m) (t1, lnck))).
Proof.
  intros.
   destruct k.
    destruct l.
      exact ( X , X0 ).
      exact tt.
    destruct l.
      exact ( X, X0 ).
   destruct t1 as [ tkl tkSl ].
    simpl.
    split.
    refine ( nckls_step _ _ _ _ _ (fst X) (fst X0) ).
    refine ( nckls_step _ _ _ _ _ (snd X) (snd X0) ).
Defined.

(*
Fixpoint lnck_fst { k l m : nat } :
  forall LNCK : lList (nCkType (S k) (S l)) m,     
     lSect (nckt_nck_l LNCK) -> lSect (nckt_nck_l (l_Lfst LNCK)).
Proof.
  intros.
  destruct m.
    exact tt.
    simpl.
    destruct X as [ [ X1a X1b ] X2 ].
    refine ( X1a , lnck_fst _ _ _ _ X2).
Defined.

Fixpoint lnck_snd { k l m : nat } :
  forall LNCK : lList (nCkType (S k) (S l)) m,     
     lSect (nckt_nck_l LNCK) -> lSect (nckt_nck_l (l_Lsnd LNCK)).
Proof.
  intros.
  destruct m.
    exact tt.
    simpl.
    destruct X as [ [ X1a X1b ] X2 ].
    refine ( X1b , lnck_snd _ _ _ _ X2 ).
Defined.
*)

Fixpoint nckls_lncks { k l m : nat }:
  forall LNCK : lList (nCkType k l) m ,
    lSect (nckt_nck_l LNCK) ->
      nCkSect (lt_l_nck (l_nck_nck_l LNCK)).
Proof.
  intros.
  destruct m.
   exact (noneOfAnything LNCK).
   destruct LNCK as [ t1 lnck ].
  refine (nckls_step _ _ (fst X)
                 (nckls_lncks _ _ _ _ (snd X))).
Defined.

Fixpoint fstpair_elim { n k } :
forall { A : nCkType n k }
 {B : Type}{ b : nCkList B n k},
  nCkSect A ->
    nCkSect (nCkT_S (nCkLfst (nCkLPair A b ))).
Proof.
  intros.
  destruct n.
    destruct k.
      exact X.
      exact tt.
    destruct k.
      exact X.
      simpl. destruct A. destruct b.
      exact (fstpair_elim _ _ _ _ _ (fst X),
             fstpair_elim _ _ _ _ _ (snd X)).
Defined.

Fixpoint sndpair_elim { n k } : 
forall { A: Type } { a : nCkList A _ _ }
 { B : nCkType n k },
 nCkSect B -> (nCkSect (nCkT_S (nCkLsnd (nCkLPair a B)))).
Proof.
  intros.
  destruct n.
    destruct k.
      exact X.
      exact tt.
    destruct k.
      exact X.
      destruct a, B.
      exact (sndpair_elim _ _ _ _ _ (fst X),
             sndpair_elim _ _ _ _ _ (snd X)).
Defined.

(*
Fixpoint nckls_lncks_alt { k l m : nat }:
  forall LNCK : lList (nCkType k l) m, 
    lSect (nckt_nck_l LNCK) ->
      nCkSect (lt_l_nck_alt (ln_nl_alt LNCK)).
Proof.
  intros.
  destruct m.
    exact (nCkKonst tt _ _).
    destruct LNCK.
    destruct X.
    apply nCkPair.
    simpl.
     apply fstpair_elim.
     exact n0.
    simpl.
    refine (nckls_lncks_alt _ l _ _ l1).
    apply sndpair_elim.
    apply 
      (nckls_lncks_alt _ _ _ l0 l1).
*)
