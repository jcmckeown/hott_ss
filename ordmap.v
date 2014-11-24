Require Import HoTT.
Require Import Nat.
Require Import nCk.

Definition LT (m : nat) := sigT (lt m).

Definition LT_S {m : nat} : LT m -> LT (S m).
Proof.
  intros [k ord].
  exists k.
  exact ( lt_trans (lt_S m) ord).
Defined.

Definition LT_Top (m : nat) : LT (S m) :=
  existT _ m (lt_S m).

Definition idx { m : nat }(k : LT m) : nat :=
  projT1 k.

Definition lt_Lt { m : nat } (k l : LT m) :=
  lt ( idx k ) (idx l).

Definition lt_Lt_trans { n : nat } { k l m : LT n } :
 lt_Lt k l -> lt_Lt l m -> lt_Lt k m.
Proof.
  apply lt_trans.
Defined.

Lemma eq_m_eq { n : nat } { k l : LT n } :
  idx k = idx l -> k = l.
Proof.
  intro.
  destruct k. destruct l. simpl in H.
  destruct H. apply ap.
  apply hset_lt.
Defined.

Lemma dec_eq_mval { l : nat } : decidable_paths (LT l).
Proof.
  intros x y.
  destruct ( dec_eq_nat (idx x) (idx y) ).
    left.
    apply eq_m_eq. auto.
    right.
    intro. apply n.
    apply ap. auto.
Defined.

(** a gritty, fluffy space covering m -Choose- n ; --- it's hard
to prove equations in this space ~~ one needs at least a
finitary Funext.
 *)

Definition ordMap (m n : nat) :=
  { f : (LT n) -> (LT m) &
         forall k k' : LT n,
          lt_Lt k k' -> lt_Lt (f k) (f k') }.

Lemma ordCompose { l m n : nat } :
  ordMap l m -> ordMap m n -> ordMap l n.
Proof.
  intros [ f ordf ] [ g ordg ].
  exists (compose f g).
  intros.
  unfold compose.
    apply ordf.
    apply ordg.
    auto.
Defined.

Lemma ordS {m : nat} : ordMap (S m) m.
Proof.
  exists LT_S.
  intros.
  destruct k as [k ordk].
  destruct k' as [l ordl].
  auto.
Defined.

Lemma ordS_bound { m : nat } :
  forall k, 
  lt_Lt (LT_Top m) (ordS .1 k).
Proof.
  intros.
  destruct k.
  unfold lt_Lt.
  unfold LT_Top.
  simpl. auto.
Defined.

Lemma ordZ m : ordMap m 0.
Proof. unfold ordMap.
  exists (fun k : LT 0 => 
    let ( a , no ) := k in match no return LT m with end 
   ).
  intro k.
  destruct k as [ _ [ ] ].
Defined.

Lemma zNOrd { k : nat } : ordMap 0 (S k) -> Empty.
Proof.
  intros [ f _ ].
  destruct ( f (LT_Top k)) as [ _ [ ] ].
Defined.

(**
Next thing would be to build the section-retract pair that makes 
everything ever more reasonable... ?
***********************)

Lemma ordAdd { d m : nat } :
  ordMap (add d m) m.
Proof.
  induction d.
  exists idmap.
  auto.
  simpl.
  apply (ordCompose ordS).
  auto.
Defined.

(** 
Lemma ordEmbed { l m : nat } :
  (lt (S l) m) -> ordMap l m.
Proof.
  revert l.
  induction m.
  intros. apply ordZ.
  intros.
    set (help := 
  destruct X.
  intros.
  exists ( ordAdd 
  rewrite <- (ap predec eq : add m dif =  l).
  rewrite add_Sym.
  apply ordAdd.
Defined.
*)

Lemma ordTruncate { l m : nat } (f : ordMap (S l) (S m)) :
  ordMap (idx (f .1 (LT_Top m))) m.
Proof.
  pose ( F' := ordCompose f ordS ).
  destruct f as [ f ord ]; simpl.
  pose ( f' := compose idx (F' .1) ).
  assert ( forall k,
   lt (idx (f (LT_Top m))) (f' k)) .
   intro.
   refine ( ord _ (ordS .1 k) _ ).
   apply ordS_bound.
  exists 
    ( fun k => ( _ ; (X k)) ).
  intros k k'.
  set (L := (f (LT_Top m))) in *.
    destruct L as [ L ordL ].
     simpl idx in X.
    unfold f'. unfold F'.
    simpl.
    unfold compose.
    intro.
    unfold lt_Lt. simpl.
    apply ord.
    apply (ordS .2). auto.
Defined.

Lemma cx_ordmap { n k : nat } : ordMap n k -> nCk n k.
Proof.
  revert n.
  induction k.
  intros.
  exact tt.
  intros.
  destruct n.
    destruct ( zNOrd X ).
  pose ( help := ordTruncate X ).
    exists ( idx (X.1 (LT_Top k))).
    split.
    destruct X as [ f ords ].
    apply IHk. auto.
    destruct X.
    simpl projT1. destruct ( x ( LT_Top k)). auto.
Defined.

(** 
 This looks about as long as the associativity of composition in the old
 "nCk.v" trial, which this is (ultimately) supposed to replace;
 however, that other required keeping well in mind the (rather obscure)
 underlying encoding, and muddling through based on guessing what would
 happen w.r.t that encoding, several steps later.
 This one should be much better motivated: it's just a translation between
 a function/list representation of the same data (though coq isn't allowed
 to believe they're "the same" on its own.); as such, we only need to
 help coq through the right parts of the underlying computation.
*)

Lemma eq_cx_ordmap { n k : nat } ( f g : ordMap n k ) :
  (f .1 == g .1 ) -> ( cx_ordmap f = cx_ordmap g ).
Proof.
  revert n f g.
  induction k.
  intros.
  auto.
  intros.
  destruct n.
    destruct ( zNOrd g ).
    destruct f as [ f ordf ].
    destruct g as [ g ordg ].
    simpl in X.
      set ( z := ( cx_ordmap (f ; ordf)) .1 ).
        simpl in z.
    refine ( 
      path_sigma _ (cx_ordmap ( f ;ordf) ) (cx_ordmap (g ; ordg))
         (ap idx (X (LT_Top k))) _ ).
    apply path_prod.
      set ( W := (X (LT_Top k))).
        set ( R := (ap idx W)) in *.
      path_via ( cx_ordmap ( ordTruncate ( g ; ordg ) ) ).
      path_via ( transport (fun z => nCk z k) 
        R (cx_ordmap (ordTruncate ( f ; ordf ) ) ) ).
      path_via ( transport (fun z => nCk z k) R
         (fst (cx_ordmap (f ; ordf ) ) .2)).      
      rewrite transport_prod. unfold fst. auto.
      set ( tf := (ordTruncate (f ; ordf)) ).
      set ( tg := (ordTruncate (g ; ordg)) ).
      simpl projT1 in *.
      path_via (cx_ordmap (transport (fun z => ordMap z k) R tf)).
        clear. destruct R. auto.
      apply IHk.
        intro.
        unfold tf, tg.
        apply eq_m_eq.
        path_via ( idx ( f (ordS .1 x) ) ).
          set (gk :=  ( idx (g (LT_Top k))) ) in *. 
          clear. destruct R. unfold transport.
            destruct x as [ l ordl ].
        auto.
          simpl.
          unfold compose.
          apply ap. auto.
   apply hset_lt.
Defined.

Lemma map_cx { n k : nat } : nCk n k -> LT k -> LT n.
Proof.
  revert n.
  induction k.
  intros.
    destruct X0 as [ _ []].
  intros.
    destruct X as [ l [ cx ord ]].
    destruct X0 as [ m ordm ].
    destruct ( dec_eq_nat m k ).
      exists l. auto.
        destruct (opt_ltS ordm).
          destruct p. destruct (n0 idpath).
      destruct ( IHk l cx ( m ; l0 ) ) as [ ans ordA ].
      exists ans.
      refine ( lt_trans ord ordA ).
Defined.

Lemma ordM_cx { n k : nat } : nCk n k -> ordMap n k.
Proof.
  intro.
  exists (map_cx X).
  revert n X.
  induction k.
  intros.
    destruct k as [ _ []].
  intros.
    destruct k0 as [ k0 ord0 ].
    destruct k' as [ k1 ord1 ].
    unfold lt_Lt in X0.
      simpl in X0.
    destruct X as [ l [ cx ord ] ].
    simpl.
    destruct (dec_eq_nat k0 k).
     destruct (dec_eq_nat k1 k). (** actually only one consistent case*)
      destruct p0.
        assert ( lt k0 k0 ).
         exact ( transport (lt k0) (inverse p) X0).
         destruct ( nLt_xx X ).
     destruct ( opt_ltS ord1 ).
      destruct ( n0 (inverse p0)).
      destruct ( map_cx cx (k1 ; l0) ).
      exact l1. (** we've dealt with all the sub-cases of (k0 = k) *)
     destruct ( opt_ltS ord0 ).
        destruct ( n0 (inverse p)).
     destruct ( dec_eq_nat k1 k).
     (** S k > k0 > k1 = k => contradiction *)
        assert ( wrong := lt_strongTrans ord0 X0 ).
          destruct p.
          destruct (nLt_xx wrong).
     destruct (opt_ltS ord1).
        destruct ( n1 (inverse p)).
     assert ( ans := IHk _ cx ( k0 ; l0) (k1 ; l1 ) X0).
    destruct ( map_cx cx (k0 ; l0 )).
    destruct ( map_cx cx (k1; l1)).
    auto.
Defined.

Definition nCkCompose { k l m } : nCk k l -> nCk l m -> nCk k m.
Proof.
  intros.
  apply cx_ordmap.
  exact (ordCompose (ordM_cx X) (ordM_cx X0)).
Defined.
