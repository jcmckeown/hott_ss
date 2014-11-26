Require Import HoTT.
Require Import Nat.
Require Import nCk.

Local Open Scope path_scope.

Definition LT (m : nat) := sigT (lt m).

Definition LT_S {m : nat} ( x : LT m) : LT (S m) :=
  ( x .1 ; lt_trans (lt_S m) x.2 ).

Definition LT_Top (m : nat) : LT (S m) :=
  existT _ m (lt_S m).

Definition idx { m : nat }(k : LT m) : nat :=
  projT1 k.

Definition LT_plus { l : nat } : LT l -> LT (S l).
Proof.
  intros [ k ordk ].
  exists (S k).
  auto.
Defined.

Definition LT_z (l : nat) : LT (S l) :=
  ( 0 ; tt ).

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

Fixpoint nat_cx_lt { n k : nat } : nCk n k -> LT k -> nat :=
  match k with
  | O => fun _ => fun z : LT 0 => match z with ( q ; p ) => match p : lt 0 q with end end
  | S k' =>
    fun cx : nCk n (S k') =>
      match cx with
      ( m ; ( cx' , ord)) =>
      fun l : LT (S k') =>
        match l with ( l' ; ordl ) => 
          match ( @opt_ltS k' l' ordl) with
          | inl _ => m
          | inr ordq => 
            nat_cx_lt cx' (l' ; ordq ) end end end end.

Lemma map_cx { n k : nat } : nCk n k -> LT k -> LT n.
Proof.
  intros.
  exists (nat_cx_lt X X0).
  revert n X X0.
  induction k.
  intros.
    destruct X0 as [ _ [] ].
  intros.
    destruct X0.
    simpl.
    destruct X as [ m [ cx nm ]].
    destruct (opt_ltS l).
    auto.
    apply (lt_trans nm).
    apply IHk.
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
    unfold map_cx.
    unfold lt_Lt. simpl.
   destruct (opt_ltS ord0 ).
    destruct p.
     destruct ( opt_ltS ord1 ).
      destruct p. destruct (nLt_xx X0).
     destruct k. destruct X0.
     destruct l. destruct (lt_nck cx).
     set (help := (map_cx cx (k1 ; l0)) .2).
      auto.
    destruct ( opt_ltS ord1 ).
      destruct p.
      destruct ( nLt_xx (lt_trans X0 l0)).
    exact (IHk _ cx (k0 ; l0) (k1 ; l1) X0 ).
Defined.

Definition nCkCompose { k l m } : nCk k l -> nCk l m -> nCk k m.
Proof.
  intros.
  apply cx_ordmap.
  exact (ordCompose (ordM_cx X) (ordM_cx X0)).
Defined.

Lemma map_idx_eq { k l m } { cx : nCk m l } { ord : lt k m }:
forall x : LT l,
idx (map_cx cx x) = idx (@map_cx k (S l) (m ; (cx, ord)) (LT_S x)).
Proof.
  intros.
    unfold idx. unfold map_cx. unfold projT1.
  revert k m cx ord x.
  destruct l.
    intros _ _ _ _ [ _ []].
  intros.
    destruct x as [ n ordn ].
      unfold LT_S. simpl projT1. simpl projT2.
      destruct n. simpl. destruct ordn. auto.
    unfold nat_cx_lt.
    destruct ( opt_ltS (lt_trans (lt_S _ ) ordn)).
      destruct ( nLt_xx (transport _ (p ^) ordn)).
    destruct cx as [ p [ cx mp ]].
      assert ( w : ordn = l0 ). apply hset_lt. destruct w.
     destruct (opt_ltS ordn). auto.
     auto.
Defined.
    
Lemma eq_map_cx { k l } {a b : nCk k l} :
  map_cx a == map_cx b ->
  a = b.
Proof.
  intro.
  assert ( Y : nat_cx_lt a == nat_cx_lt b ).
    intro.
    exact ( base_path ( X x )).
  clear X.
  revert k a b Y.
  induction l.
  intros.
    destruct a, b. auto.
  intros.
    destruct a as [ m [ cx orda ]].
    destruct b as [ n [ cy ordb ]].
   destruct k. destruct orda.
   assert ( h1 := Y ( l ; lt_S l )).
    simpl in h1.
    destruct ( opt_ltS (lt_S l) ). Focus 2. destruct (nLt_xx l0).
      destruct h1. apply ap.
      apply path_prod ; try apply hset_lt. simpl.
    apply IHl.
      intro.
      refine (_ @ Y (LT_S x) @ _ ).
      apply map_idx_eq.
      symmetry. apply map_idx_eq.
Defined.

Lemma om_cx_om { k l } ( w : ordMap k l ) :
  (ordM_cx (cx_ordmap w)) .1 == w .1 .
Proof.
  unfold ordM_cx. unfold projT1.
    fold ( w .1 ).
    intro m.
    apply eq_m_eq.
    unfold idx. unfold map_cx. unfold projT1.
     fold ( w .1 ).
     fold ( (w .1 m ) .1 ).
  destruct w as [ fw ordw ].
  revert k fw ordw m.
  induction l.
  intros.
  destruct m as [ _ []].
  intros.
    destruct m as [ m lm ].
    unfold projT1 at 2.
    destruct k.
      destruct ( fw (LT_z l) ) as [ _ []].
    simpl.
    destruct ( opt_ltS lm ). destruct p.
    unfold LT_Top.
      assert ( lm = lt_S l ).
        apply hset_lt.
      destruct X. auto.
    unfold compose. unfold idx.
    refine ( IHl _ _ _ (m ; l0) @ _ ).
    unfold projT1.
    refine ( base_path ( _ : fw (LT_S  (m ; l0)) = fw ( m ; lm )) ).
    apply ap.
    unfold LT_S . simpl projT1.
    apply ap.
    apply hset_lt.
Defined.
  
Lemma nCkAssoc { k l m n } ( f : nCk k l ) (g : nCk l m) (h : nCk m n) :
  nCkCompose f (nCkCompose g h) = nCkCompose (nCkCompose f g) h.
Proof.
  unfold nCkCompose.
  path_via 
    (cx_ordmap (ordCompose (ordM_cx f) 
      (ordCompose (ordM_cx g) (ordM_cx h)))).
    apply eq_cx_ordmap.
    intro.
    path_via ( (ordM_cx f) .1 
      (( ordM_cx (cx_ordmap (ordCompose (ordM_cx g) (ordM_cx h)))) .1 x )).
    path_via ( (ordM_cx f) .1 ( (ordCompose (ordM_cx g) (ordM_cx h)) .1 x)).
    apply ap.
    apply om_cx_om.
  apply eq_cx_ordmap.
  intro.
  path_via 
     ((ordM_cx (cx_ordmap (ordCompose (ordM_cx f) (ordM_cx g)))).1 ((ordM_cx h) .1 x)).
  path_via ( (ordCompose (ordM_cx f) (ordM_cx g)) .1 ((ordM_cx h) .1 x)).
  symmetry.
  apply om_cx_om.
Defined.
