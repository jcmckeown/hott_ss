Require Import HoTT.

Local Open Scope path_scope.

Definition predec (n : nat) :=
  match n with
  | O => O
  | S m => m end.

Definition zNSuc (P : nat -> Type) (n : nat)
  (wrong : O = S n) : (P (S n)) :=
  transport (fun z =>
    match z with
    | O => Unit
    | S m => P (S m) end) wrong tt.

Definition SucNZ (P : nat -> Type) (n : nat)
  (wrong : S n = O) : (P (S n)) := zNSuc P n (wrong ^).

Definition eq_inherit (a b : nat) (decn : (a = b) \/ (~ a = b)) :
  ( (S a = S b) \/ ( ~ S a = S b ) ) :=
match decn with
  | inl eq => inl (ap S eq)
  | inr refut => inr (fun eqn : S a = S b => refut (ap predec eqn)) end.

Fixpoint dec_eq_nat (a b : nat) : (a = b) \/ ( ~ a = b ) :=
  match a with
  | O =>
    match b with
    | O => inl idpath 
    | S m => inr (zNSuc (fun _ => Empty) m) end
  | S k =>
    match b with
    | O => inr ( SucNZ (fun _ => Empty) k )
    | S l => eq_inherit k l (dec_eq_nat k l) end end.

Definition hset_nat := hset_decidable dec_eq_nat.

Fixpoint add (m n : nat) :=
  match m with
   | O => n
   | S m' => S (add m' n) end.

Lemma add_S m n : add m (S n) = S (add m n).
Proof.
  induction m.
  auto.
  exact (ap S IHm).
Defined.

Lemma add_Sym m n : add m n = add n m.
Proof.
  induction n.
    path_via m.
    induction m.
      auto.
      exact (ap S IHm).
    path_via (S (add m n)).
    apply add_S.
    refine (ap S _).
    auto.
Defined.

Lemma add_assoc l m n : add l (add m n) = add (add l m) n.
Proof.
  induction l.
  auto.
  apply (ap S). auto.
Defined.