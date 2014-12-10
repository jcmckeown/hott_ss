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
(**
*)

Fixpoint LT (m : nat) : Type :=
  match m with
  | O => Empty 
  | S m' => sum Unit (LT m') end.

Definition LT_S { m : nat } :
  LT m -> LT (S m) := inr.

Fixpoint LT_plus { m : nat } :
  LT m -> LT (S m) :=
 match m with
 | O => fun x => match x with end
 | S m' =>
  fun x =>
    match x with 
    | inl _ => inl tt
    | inr x => inr (LT_plus x) end end.

Definition LT_Top (m : nat) : LT (S m) := inl tt.

Fixpoint LT_z (m : nat) : LT (S m) :=
  match m with
  | O => inl tt
  | S m' => inr (LT_z m') end.

(*

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
*)

Fixpoint idx { m : nat } : 
  LT m -> nat :=
match m with
 | O => fun x => match x with end
 | S m' =>
  fun x => 
  match x with
    | inl _ => m'
    | inr x' => idx x' end end.

Fixpoint idx_lt { m : nat } :
  forall z : LT m,
    lt m (idx z).
Proof.
  destruct m.
  intros [].
  intros.
  destruct z.
  apply lt_S.
  refine (lt_trans (lt_S _) _).
  simpl.
  apply idx_lt.
Defined.

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
  induction n.
    destruct l.
  intros.
    destruct k.
    destruct l.
      destruct u; destruct u0; auto.
      destruct u. simpl in H.
      destruct
        (nLt_xx (transport (fun z => lt n z) H^ (idx_lt l))).
    destruct l.
      simpl in H.
        destruct (nLt_xx (transport (lt n) H (idx_lt l0))).
      simpl in H.
      apply ap.
      apply IHn.
      auto.
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

Fixpoint lLT (T : Type) (l : nat) : lType l :=
  match l with
  | O => tt
  | S l' => ( T , lLT T l' ) end.

Fixpoint l_monOp (W : Type -> Type) { l : nat } :
  lType l -> lType l :=
  match l return lType l -> lType l with
  | O => fun _ => tt
  | S l' => fun X : lType (S l') => ( W (fst X), l_monOp W (snd X)) end.

Fixpoint l_pairOp (W : Type -> Type -> Type) { l : nat } :
 lType l -> lType l -> lType l :=
match l return lType l -> lType l -> lType l with
  | O => fun _ _ => tt
  | S l' => fun Ta Tb => 
    ( W (fst Ta) (fst Tb) , l_pairOp W (snd Ta) (snd Tb)) end.

Definition l_prod { l } ( A B : lType l ) := (l_pairOp prod A B).
Definition l_sum { l } ( A B : lType l ) := (l_pairOp sum A B).
Definition l_map { l } ( A B : lType l ) := (l_pairOp (fun X Y => X -> Y) A B).

Definition lList := (fun A => fun l => lSect (lLT A l)).

Fixpoint lKonst { A: Type } (a : A) l : lList A l :=
  match l with
  | O => tt
  | S l' => ( a, lKonst a l') end.

Fixpoint lKMap { A B : Type }(f : A -> B) l : 
  lSect (l_map (lLT A l) (lLT B l)) :=
  match l with
  | O => tt
  | S l' => ( f , lKMap f l' ) end.

Fixpoint lT_fun { l : nat } : 
( LT l -> Type ) -> lType l :=
match l return ( LT l -> Type) -> lType l with
 | O => fun _ => tt
 | S l' => fun f : LT (S l') -> Type =>
   ( f ( LT_Top _ ) , lT_fun ( f o LT_S) ) end.

Fixpoint lS_fun { l : nat } :
  forall { T : LT l -> Type }, ( forall z, T z ) ->  lSect (lT_fun T) :=
match l return ( forall T : LT l -> Type, (forall z, T z) -> lSect (lT_fun T) )
 with
 | O => fun _ _ => tt
 | S l' => 
  fun T : (LT (S l') -> Type ) =>
    fun f : forall z, T z =>
     ( f ( LT_Top _ ) , lS_fun ( fun r : LT l' => f (LT_S r) ) ) end.

Fixpoint lS_eqn { l : nat } :
  forall { T : LT l -> Type }, forall {f g : forall z, T z },
   f == g -> ( lS_fun f = lS_fun g ) :=
match l return ( forall { T : LT l -> Type }, forall {f g : forall z, T z },
   f == g -> ( lS_fun f = lS_fun g ) ) with
 | O => fun T f g h => @idpath _ tt
 | S l' => fun T f g h =>
  @path_prod _ _ (lS_fun f) (lS_fun g)
    (h (LT_Top _)) (lS_eqn (fun z => h (LT_S z))) end.

Fixpoint lS_map { l : nat } : 
 forall { U V : LT l -> Type } ( f : forall z, U z -> V z ),
 ( lSect ( lT_fun U ) ) -> ( lSect (lT_fun V) ).
Proof.
  destruct l as [ | l'].
  intros U V f s.
  exact tt.
  intros U V f s.
  destruct s as [ s0 s' ].
  exact ( f _ s0 , lS_map l' _ _ (fun z => f ( LT_S z)) s' ).
Defined.

Fixpoint lT_map { l : nat } :
  forall { U : LT l -> Type } (f : forall z, U z -> Type) ,
  ( lSect ( lT_fun U ) ) -> lType l.
Proof.
  destruct l as [ | l' ].
  intros U f s.
  exact tt.
  intros U f [ s0 s' ].
  exact ( f _ s0 , lT_map l' _ (fun z => f (LT_S z)) s').
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
  exact ( fst h , lS_tMap _ _ (fun z => f (LT_S z)) (fun z => s (LT_S z)) (snd h) ).
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
  exact ( fst h, lS_Mapt _ _ (fun z => f (LT_S z)) (fun z => s (LT_S z)) (snd h)).
Defined.

Fixpoint fun_lS { l : nat } :
  forall (U : LT l -> Type ), lSect (lT_fun U) -> forall z, U z.
Proof.
  destruct l.
  intros U f [].
  intros U f z.
  destruct z as [ [] | z ].
  simpl in *.
  exact ( fst f ).
  refine (fun_lS l _ (snd f) z ).
Defined.

Fixpoint fun_lT { l : nat } :
  (lType l) -> (LT l) -> Type.
Proof.
  destruct l.
    intros _ [ ].
    intros T z.
    destruct z.
      exact (fst T).
      exact (fun_lT l (snd T) l0).
Defined.

Fixpoint lS_fun' { l : nat } :
  forall ( T : lType l ),
    (forall z, (fun_lT T) z) -> lSect T.
Proof.
  destruct l.
  intros. exact tt.
  intros.
  destruct T as [ T0 T ].
  split.
  exact ( X (LT_Top _)).
  exact ( lS_fun' _ T (fun z => X (LT_S z))).
Defined.

Fixpoint lT_S { l : nat } :
  lList Type l -> lType l :=
match l return (lList Type l -> lType l) with
| O => fun _ => tt
| S l' =>
  fun L : lList Type (S l') => 
    ( fst L , lT_S (snd L)) end.

Fixpoint lS_T { l : nat } :
  lType l -> lList Type l :=
match l return (lType l -> lList Type l) with
| O => fun _ => tt
| S l' =>
  fun L : lType (S l') => 
    ( fst L , lS_T (snd L)) end.

Fixpoint l_LPair { A B : Type } { l } : 
  lList A l -> lList B l -> lList ( A * B ) l :=
match l return lList A l -> lList B l -> lList ( A * B ) l with
| O => fun _ _ => tt
| S l' =>
  fun aa bb => ( ( fst aa, fst bb ), l_LPair (snd aa) (snd bb)) end.

Fixpoint l_Lfst { A B : Type } { l : nat } :
  lList (A * B) l -> lList A l :=
match l with
 | O => fun _ => tt
 | S l' => fun W => 
  (fst (fst W) , l_Lfst (snd W) ) end.

Fixpoint l_Lsnd { A B : Type } { l : nat } :
  lList (A * B) l -> lList B l :=
match l with
 | O => fun _ => tt
 | S l' => fun W =>
  (snd (fst W), l_Lsnd (snd W) ) end.

Fixpoint lf_t_elim { l : nat } :
  forall T : LT l -> Type,
    forall z, T z ->
      fun_lT (lT_fun T) z.
Proof.
  induction l.
  intros.
    destruct z.
  intros.
    destruct z.
      simpl. destruct u. exact X.
      simpl.
      unfold compose.
      auto.
Defined.

