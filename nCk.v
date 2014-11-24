Require Import HoTT.
Require Import Nat.

Local Open Scope path_scope.

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

Fixpoint nCk (n k : nat) : Type :=
  match k with
  | O => Unit
  | S k' => { l : nat & ( nCk l k' * lt n l ) } end.

Lemma lt_nck { k l } : nCk k l -> lt (S k) l.
Proof.
  revert k.
  induction l.
  auto.
  intros.
    destruct X as [ m [ cx ord ]].
    simpl.
  exact ( lt_strongTrans (ord : lt (S k) (S m)) (IHl _ cx) ).
Defined.

Lemma dec_eq_nCk {n k : nat} (cx cy : nCk n k) :
  ( cx = cy ) \/ ~ ( cx = cy ).
Proof.
  revert n cx cy.
  induction k.
  intros.
    destruct cx, cy. auto.
  intros.
  destruct n. destruct cx. destruct p. destruct l.
  destruct cx as [ l [ cx ordl ]].
  destruct cy as [ m [ cy ordm ]].
    destruct ( dec_eq_nat l m ).
    destruct p.
    destruct ( IHk _ cx cy ).
      left.
      apply ap.
      apply path_prod. auto.
      apply hset_lt.
      right.
        intro.
        apply n0.
        refine ( _ @ ap fst (fiber_path X)).
        refine ( @transport ( l = l ) (fun z => cx = fst (transport _ z (cx, ordl)))
                  idpath _ _ idpath ).
        apply hset_nat.
    right.
      intro.
      apply n0.
      exact ( base_path X ).
Qed.

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
