Require Import HoTT.

(** a characterization of the relations (dependent types over simple products)
that represent Functions.
*)

Local Open Scope path_scope.

Definition sigMap { A B : Type } ( P : A -> B -> Type )
  : { y : A * B & P (fst y) (snd y) } -> A.
Proof.
  intros [ [ a _ ] _ ].
  auto.
Defined.

Definition IsFunctional { A B : Type } ( P : A -> B -> Type ) 
  := 
  IsEquiv (sigMap P).

Definition underlyingFunction { A B : Type } 
 ( P : A -> B -> Type )
 : ( IsFunctional P ) -> A -> B.
Proof.
  intros [ inv retr sect adj ] a.
  exact (snd (projT1 (inv a))).
Defined.

Definition valPath { A B } ( f : A -> B ) :
 A -> B -> Type :=
  fun a => fun b => ( b = f a ).

Definition valSectn { A B } ( f : A -> B ) :
  A -> { ab : A * B & (valPath f) (fst ab) (snd ab) }.
Proof.
  intro a.
  exists ( a, f a ).
  exact idpath.
Defined.

Lemma isfunc_valpath { A B } ( f : A -> B ) :
  IsFunctional (valPath f).
Proof.
  apply isequiv_adjointify with (valSectn f).
  intro.
    auto.
    intro.
    destruct x.
    destruct x as [ a b ].
    simpl in *.
    unfold valPath in v.
   assert 
    ( @paths { z : B & z = f a } ( f a ; idpath ) ( b ; v ) ).
      apply path_sigma with (inverse v).
      simpl. destruct v. auto.
   refine ( transport (fun bp : { z : B & z = f a } =>
    valSectn f a = ( ( a , bp .1 ) ; bp .2 ) ) X _ ).
    exact idpath.
Defined.

Lemma htp_valpath { A B } ( f : A -> B ) :
  f == (underlyingFunction (valPath f) (isfunc_valpath f)).
Proof.
  intro. auto.
Defined.

Lemma map_valpath { A B } ( P : A -> B -> Type ) ( H : IsFunctional P ) :
  forall a b, ( valPath (underlyingFunction P H) a b ) ->  ( P a b ).
Proof.
  intros.
  destruct H as [ inv sect retr adj ].
    simpl in X.
    assert ( heq := sect a ).
    cbv in X. cbv.
    destruct (inv a) as [ [ r s ] t ].
      simpl in *. cbv.
      destruct X. destruct heq. auto.
Defined.

Lemma inv_valpath { A B } ( P : A -> B -> Type ) ( H : IsFunctional P ) :
  forall a b, (P a b) -> ( valPath (underlyingFunction P H) a b ).
Proof.
  intros.
  destruct H as [ inv sect retr adj ].
  simpl in *.
  lazy.
   set ( thePoint := @existT (A * B) (fun z => P (fst z)(snd z)) (a,b) X ).
    assert ( help := retr thePoint ).
    assert ( helq := ap snd (ap (@projT1 _ _) help ) ).
      lazy in helq.
  exact (inverse helq).
Defined.

Lemma hfibr_IsFunc { A B } ( P : A -> B -> Type ) ( H : IsFunctional P ) : 
  forall a, (sigT (P a)) -> hfiber (sigMap P) a.
Proof.
  intros a [ b x ].
  exists (@existT _ (fun z => P (fst z) (snd z)) (a,b) x).
  auto.
Defined.

Lemma fibrMap_IsFunc { A B } ( P : A -> B -> Type ) ( H : IsFunctional P ) : 
  forall a,  hfiber (sigMap P) a -> (sigT (P a)) .
Proof.
  intros a [ abp eq ].
  destruct abp as [ [ a' b' ] x ].
  simpl in eq. destruct eq.
  exists b'. auto.
Defined.

Lemma equiv_hfibr_IsFunc { A B } ( P : A -> B -> Type ) ( H : IsFunctional P ) : 
  forall a, IsEquiv (hfibr_IsFunc P H a).
Proof.
  intros.
  apply isequiv_adjointify with (fibrMap_IsFunc P H a).
  intro.
    destruct x as [ [ [ a' b' ] p ] eq ].
    simpl in *.
    destruct eq.
    auto.
  intro.
    destruct x as [ b x ].
    auto.
Defined.

Lemma contr_IsFunc { A B } ( P : A -> B -> Type ) ( H : IsFunctional P ) : 
  forall a, Contr (sigT (P a)).
Proof.
  assert ( help := fcontr_isequiv _ H ).
  intro a.
    set ( theEquiv := BuildEquiv _ _ (hfibr_IsFunc P H a) (equiv_hfibr_IsFunc P H a) ).
  refine ( contr_equiv (theEquiv ^-1)%equiv).
Defined.

