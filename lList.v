Require Import HoTT
 Nat.

Fixpoint lt (n k : nat) : Type :=
  match n with
  | O => Empty
  | S n' => match k with
    | O => Unit
    | S k' => (lt n' k') end end.

Fixpoint lt_b (n k : nat) : Bool :=
  match n with
  | O => false
  | S n' => match k with
    | O => true
    | S k' => (lt_b n' k') end end.

Lemma hset_lt (n k : nat) : IsHProp (lt n k).
Proof.
  revert k.
  induction n.
  intros k x y.
    destruct x.
  intros k x y.
    destruct k.
      simpl in x, y.
        destruct x.
        exists (eta_unit _).
        intro. 
        apply path2_contr.
      simpl in x, y.
      apply IHn.
Defined.

Lemma lt_trans {k l m : nat} : lt k l -> lt l m -> lt k m.
Proof.
  revert l m.
  induction k.
  intros.
  destruct X.
  intros.
    destruct l.
      destruct X0.
    destruct m.
      exact tt.
      exact (IHk l m X X0).
Defined.

Lemma ltz_lt { k l } : lt k l -> lt k 0.
Proof.
  destruct k.
  intros [].
  intros. exact tt.
Defined.

Lemma lt_strongTrans { k l m } : lt k l -> lt l m -> lt k (S m).
Proof.
  revert k l.
  induction m.
  intros.
    destruct k.
      destruct X.
    destruct l. destruct X0.
    simpl.
    simpl in X.
    exact ( ltz_lt X ).
  intros.
    destruct k. destruct X.
    destruct l. destruct X0.
    simpl in *.
    exact (IHm _ _ X X0).
Defined.

Fixpoint lt_S (k : nat) : lt (S k) k :=
  match k with
| O => tt
| S k' => (lt_S k') end.

Lemma opt_ltS { m n } : lt (S m) n -> ( m = n ) \/ ( lt m n ).
Proof.
  revert n.
  induction m.
  intros.
    destruct n.
    auto.
    destruct X.
  intros.
    destruct n.
    right. auto.
    destruct ( IHm n X ).
    left. exact (ap S p).
    right. auto.
Defined.

Lemma nLt_xx { x : nat } : lt x x -> Empty.
Proof.
  induction x.
  auto.
  apply IHx.
Defined.

Definition LT (m : nat) := sigT (lt m).

Definition LT_S {m : nat} : LT m -> LT (S m).
Proof.
  intros [k ord].
  exists k.
  exact ( lt_trans (lt_S m) ord).
Defined.

Definition LT_Top (m : nat) : LT (S m) :=
  existT _ m (lt_S m).

Definition LT_plus { l : nat } : LT l -> LT (S l).
Proof.
  intros [ k ordk ].
  exists (S k).
  auto.
Defined.

Definition LT_z (l : nat) : LT (S l) :=
  ( 0 ; tt ).

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

(* ~~~~~ *)

Fixpoint lType (l : nat) : Type :=
  match l with
  | 0 => Unit
  | S l' => Type * lType l' end.

Fixpoint lSect { l : nat } : lType l -> Type :=
  match l return (lType l -> Type) 
  with
  | O => fun _ => Unit
  | S l' =>
    fun ( T : Type * lType l' ) =>
      let ( t , T' ) := T in t * lSect T' end.

Fixpoint lT_fun { l : nat } : 
( LT l -> Type ) -> lType l :=
match l return ( LT l -> Type) -> lType l with
 | O => fun _ => tt
 | S l' => fun f : LT (S l') -> Type =>
   ( f ( LT_z _ ) , lT_fun ( f o LT_plus) ) end.

Fixpoint lS_fun { l : nat } :
  forall { T : LT l -> Type }, ( forall z, T z ) ->  lSect (lT_fun T) :=
match l return ( forall T : LT l -> Type, (forall z, T z) -> lSect (lT_fun T) )
 with
 | O => fun _ _ => tt
 | S l' => 
  fun T : (LT (S l') -> Type ) =>
    fun f : forall z, T z =>
     ( f ( LT_z _ ) , lS_fun ( fun r : LT l' => f (LT_plus r) ) ) end.

Fixpoint lS_eqn { l : nat } :
  forall { T : LT l -> Type }, forall {f g : forall z, T z },
   f == g -> ( lS_fun f = lS_fun g ) :=
match l return ( forall { T : LT l -> Type }, forall {f g : forall z, T z },
   f == g -> ( lS_fun f = lS_fun g ) ) with
 | O => fun T f g h => @idpath _ tt
 | S l' => fun T f g h =>
  @path_prod _ _ (lS_fun f) (lS_fun g)
    (h (LT_z _)) (lS_eqn (fun z => h (LT_plus z))) end.

Notation lList T l :=
  (@lSect l (lT_fun (fun _ => T))).

Notation lTKonst a l :=
  ( @lS_fun l ( fun _ => _ ) (fun _ => a) ).

Fixpoint lS_map { l : nat } : 
 forall { U V : LT l -> Type } ( f : forall z, U z -> V z ),
 ( lSect ( lT_fun U ) ) -> ( lSect (lT_fun V) ).
Proof.
  destruct l as [ | l'].
  intros U V f s.
  exact tt.
  intros U V f s.
  destruct s as [ s0 s' ].
  exact ( f _ s0 , lS_map l' _ _ (fun z => f ( LT_plus z)) s' ).
Defined.

Fixpoint lT_map { l : nat } :
  forall { U : LT l -> Type } (f : forall z, U z -> Type) ,
  ( lSect ( lT_fun U ) ) -> lType l.
Proof.
  destruct l as [ | l' ].
  intros U f s.
  exact tt.
  intros U f [ s0 s' ].
  exact ( f _ s0 , lT_map l' _ (fun z => f (LT_plus z)) s').
Defined.

Fixpoint lS_tMap { l : nat } :
 forall {U : LT l -> Type }
  { f : forall z, U z -> Type }
  { s : forall z, U z  }
  (h : lSect ( lT_fun (fun z => f z ( s z )) )),
 lSect ( lT_map f (lS_fun s) ).
Proof.
  destruct l as [ | l' ].
  intros.
  exact tt.
  intros.
  exact ( fst h , lS_tMap _ _ (fun z => f (LT_plus z)) (fun z => s (LT_plus z)) (snd h) ).
Defined.

Fixpoint lS_Mapt { l : nat } :
  forall { U : LT l -> Type }
   { f : forall z, U z -> Type }
   { s : forall z, U z } 
  ( h : lSect (lT_map f (lS_fun s))),
  lSect (lT_fun (fun z => f z ( s z))).
Proof.
  destruct l as [ | l' ].
  intros.
  exact tt.
  intros.
  exact ( fst h, lS_Mapt _ _ (fun z => f (LT_plus z)) (fun z => s (LT_plus z)) (snd h)).
Defined.

Fixpoint fun_lS { l : nat } :
  forall (U : LT l -> Type ), lSect (lT_fun U) -> forall z, U z.
Proof.
  destruct l.
  intros U f [ _ []].
  intros U f [ z ord].
  destruct z. destruct ord. exact ( fst f ).
  refine (fun_lS l _ (snd f) (z ; ord) ).
Defined.