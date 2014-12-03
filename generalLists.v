Require Import
  HoTT
  Nat.
Require Export
  lList
  austere_nCk.

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