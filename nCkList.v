Require Import HoTT.
Require Import Nat.
Require Import ordmap.
Require Import nCk.

Open Scope path_scope.

Fixpoint lType (l : nat) : Type :=
  match l with
 | O => Unit
 | S l' => Type * (lType l') end.

Fixpoint lSect { l : nat } ( T : lType l) : Type :=
  match l , T return Type with
  | O , tt => Unit
  | S l' , ( T0 , T') => 
     ( T0 * lSect T' ) end.

Lemma lT_depT {l : nat} (P : LT l -> Type) : lType l.
Proof.
  revert P.
  induction l.
  intros.
  exact tt.
  intros.
  split.  exact ( P (LT_z l)).
  apply IHl.
  intro. exact ( P ( LT_plus X )).
Defined.

Lemma dep_lT {l : nat} : lType l -> (LT l -> Type).
Proof.
  induction l.
  intros.
  destruct X0 as [ _ []].
  intros T k.
    destruct T as [ T0 T ].
    destruct k as [ k ordk ].
     destruct k. exact T0.
     exact (IHl T (k ; ordk)).
Defined.

Lemma depT_inv { l } ( Q : LT l -> Type ) : 
forall n, dep_lT (lT_depT Q) n = Q n.
Proof.
  revert Q.
  induction l.
  intros. destruct n as [ _ [] ].
  intros.
  destruct n as [ n ord ].
  destruct n.
    simpl.
    apply ap. destruct ord. auto.
  exact ( IHl (fun z => Q (LT_plus z)) (n ; ord) ).
Defined.

Lemma lS_depS {l : nat} {P : LT l -> Type} (p : forall n, P n) :
  lSect (lT_depT P).
Proof.
  induction l.
  exact tt.
  split.
  apply p.
  auto.
Defined.

Lemma lS_depS' {l : nat} { T : lType l } ( p : forall n, dep_lT T n ) :
  lSect T.
Proof.
  induction l. destruct T.
    exact tt.
  destruct T as [ T0 T ].
  split.
  exact ( p (LT_z l) ).
  apply IHl.
  intro.
  assert ( ans := p (LT_plus n)).
    destruct n as [ n ordn ].
    auto.
Defined.

Lemma depS_lS {l : nat} {T : lType l} ( p : lSect T ) :
  forall k, (dep_lT T k).
Proof.
  revert T p.
  induction l.
  intros.
  destruct k as [ _ [] ].
  intros.
  destruct T as [ T0 T ].
  destruct k as [ k ordk ].
  destruct p as [ p0 p ].
  destruct k.
    simpl in *.
    auto.
    apply IHl. auto.
Defined.

Lemma depS_lS' { l : nat } { T : LT l -> Type }
 (p : lSect (lT_depT T)) (k : LT l) : T k.
Proof.
  revert T p k.
  induction l.
  intros.
    destruct k as [ _ [] ].
  intros.
  destruct p as [ t p ].
    destruct k as [ k ordk ].
      destruct k. destruct ordk.
      auto.
  exact  (IHl (T o LT_plus) p (k ; ordk) ).
Defined.

Lemma depS_inv {l : nat} {P : LT l -> Type} (p : forall n, P n) k:
  depS_lS' (lS_depS p) k = p k.
Proof.
  revert P p k.
  induction l.
    intros.
    destruct k as [ _ []].
  intros.
  destruct k as [ k ord ]. destruct k.
    simpl. unfold LT_z. destruct ord.
    auto.
  exact (IHl (P o LT_plus) (fun z => p (LT_plus z)) (k ; ord)) .
Defined.

Definition lMonoType ( l : nat ) (A : Type) : lType l := lT_depT (fun _ => A).
Definition lList (l : nat) (A : Type) : Type := lSect (lMonoType l A) .
Definition lKonst (l : nat) { A : Type } (a : A) : lList l A := 
  lS_depS (fun _ => a).

Definition lSType (l : nat) := lSect (lMonoType l Type).


(** I don't know if we ever need this *)
(* Lemma lT_lMono_T {l : nat} : lSType l -> lType l.
Proof.
  induction l.
  intros.
  exact tt.
  intros.
  split.
  apply X.
  apply IHl.
  apply X.
Defined.

Coercion lT_lMono_T : lSType >-> lType. *)

Lemma lProd {l : nat} (P Q : lType l) : lType l.
Proof.
  apply lT_depT.
  intro. exact ( dep_lT P X * dep_lT Q X ).
Defined.

Lemma lSum { l : nat } (P Q : lType l) : lType l.
Proof.
  apply lT_depT.
  exact (fun x => (dep_lT P x) + (dep_lT Q x)).
Defined.

Lemma lMap { l : nat } ( P Q : lType l ) : lType l.
Proof.
  apply lT_depT.
  exact (fun x => (dep_lT P x) -> (dep_lT Q x)).
Defined.

Lemma lApply { l : nat } { P Q : lType l } :
  lSect ( lMap P Q ) -> lSect P -> lSect Q.
Proof.
  intros.
  apply lS_depS'.
  intro.
  apply ( depS_lS' X n ).
  exact ( depS_lS X0 n).
Defined.

Lemma lT_MapT {l : nat} { P Q : LT l -> Type } :
  lSect (lT_depT (fun n => P n -> Q n) )
   -> lSect (lMap (lT_depT P) (lT_depT Q)).
Proof.
  unfold lMap.
  intros.
  apply lS_depS.
    intro.
    rewrite depT_inv.
    rewrite depT_inv.
    apply ( depS_lS' X).
Defined.

Lemma lPair { l : nat } { P Q : lType l }
  (p : lSect P ) (q : lSect Q) : lSect (lProd P Q).
Proof.
  apply lS_depS.
  exact ( fun x => ( depS_lS p x , depS_lS q x ) ).
Defined.

Lemma lInL { l : nat } { P : lType l} ( Q : lType l )
 ( p : lSect P ) : lSect (lSum P Q).
Proof.
  apply lS_depS.
  exact ( fun x => inl ( depS_lS p x )).
Defined.

Lemma lInR { l : nat } ( P : lType l ){ Q : lType l }
 ( p : lSect Q ) : lSect (lSum P Q).
Proof.
  apply lS_depS.
  exact ( fun x => inr (depS_lS p x)).
Defined.

Lemma listEqn { l : nat } { P : LT l -> Type } { p q : forall k , P k }:
  ( p == q ) -> ( lS_depS p = lS_depS q ).
Proof.
  revert P p q.
  induction l.
  intros. auto.
  intros.
  apply path_prod. apply X.
  simpl. apply IHl.
    intro.
    apply X.
Defined.

Lemma listEqn' { l : nat } { P : lType l } { p q : lSect P } :
  ( depS_lS p == depS_lS q ) -> p = q .
Proof.
  revert P p q.
  induction l.
  intros. destruct P. destruct p, q. auto.
  intros.
  destruct P as [ P0 P ].
  destruct p as [ p0 p ].
  destruct q as [ q0 q ].
  apply path_prod.
    simpl.
    exact ( X ( 0 ; tt )).
    simpl.
    apply IHl.
    intros [ k ord ].
    set ( Xh := X ( LT_plus ( k ; ord )) ).
    auto.
Defined.

Lemma listEqn'' { l : nat } { P : LT l -> Type } { p q : lSect (lT_depT P) } :
  ( depS_lS' p == depS_lS' q ) -> p = q.
Proof.
  revert P p q.
  induction l.
  intros.
    destruct p, q. auto.
  intros.
    destruct p as [ p0 p ].
    destruct q as [ q0 q ].
    apply path_prod.
      apply X.
      simpl.
      apply IHl.
      intros [ k ord ].
      refine ( X ( LT_plus ( k ; ord ) )).
Defined.

Fixpoint nCkList (T : Type) (k n : nat) : Type :=
  match k with
 | O => T
 | S k' => lSect ( @lT_depT n (compose (nCkList T k') idx ) ) end.

Fixpoint fun_list { T : Type } {k n : nat} : 
  nCkList T k n -> nCk n k -> T :=
  match k with
  | O => fun X cx => X
  | S k' => fun ( X : nCkList T (S k') n) (cx : nCk n (S k')) =>
    let ( l , p) := cx in
    let ( cx' , ord ) := p in
    fun_list ( depS_lS' X (l ; ord)) cx' end.

Fixpoint list_fun { T : Type }{ k n : nat } : 
  (nCk n k -> T) -> nCkList T k n :=
  match k with
  | O => (fun f : nCk n 0 -> T => (f tt))
  | S k' => (fun f : nCk n (S k') -> T =>
    lS_depS (fun l : LT n => list_fun (fun z => f ((l.1) ; (z , l.2 ))))) end.

Lemma fl_inv { T : Type } { k n : nat }
  ( X : nCk n k -> T ):
   forall y, fun_list (list_fun X) y = X y.
Proof.
  revert T n X.
  induction k.
  intros.
    destruct y.
    auto.
  intros.
    destruct y as [ l [ cx ord ]].
    simpl.
    refine ( _ @ IHk T l (fun z => X ( l ; (z,ord))) cx).
    rewrite depS_inv. destruct n.
      destruct ord.
    auto.
Defined.

Lemma lf_inv { T : Type } { k n : nat }:
  forall X : nCkList T k n, 
    list_fun (fun_list X) = X.
Proof.
  revert T n.
  induction k.
  intros.
    auto.
  intros.
  apply listEqn''.
  intros [ l ord ].
    simpl.
    rewrite depS_inv. simpl.
  refine ( _ @ IHk _ _ _ ).
  destruct n. destruct ord.
  auto.
Defined. 

(* Lemma nCkT_depT { k n : nat } : 
  (nCk n k -> Type) -> (nCkType k n).
Proof.
  revert n.
  induction k.
    intros.
    exact (X tt).
    intros.
    simpl.
    apply lS_depS.
    intros l. apply IHk.
    intro cx.
    apply X.
    exists ( idx l ).
    split.
    auto.
    exact (l .2).
Defined.

Lemma depT_nCk { k n : nat } ( T : nCkType k n ) :
  nCk n k -> Type.
Proof.
  revert n T.
  induction k.
  intros.
    exact T.
    intros m T cx.
    destruct cx as [ l [ cx ord ]].
    refine (IHk _ _ cx).
    exact (depS_lS' T ( l ; ord ) ).
Defined.

Lemma depT_nCk_inv { k n } (T : nCk n k -> Type) :
  forall x, depT_nCk ( nCkT_depT T ) x = T x.
Proof.
  revert n T.
  induction k.
  intros.
    destruct x. auto.
  intros.
    destruct x as [ l [ cx ord ]]. simpl.
    rewrite depS_inv.
    apply (IHk l (fun z => T ( l ; ( z , ord))) ).
Defined.

Definition nCkSectn {k n : nat} (T : nCkType k n) : Type.
Proof.
  revert n T.
  induction k.
  intros.
    exact T.
  intros.
   refine ( @lSect n _ ).
   apply lT_depT.
   intros [ l ord ].
   apply (IHk l).
   apply ( depS_lS' T (l ; ord) ).
Defined.

Lemma nCkS_depS { k n : nat } { T : nCk n k -> Type } 
  ( X : forall x, T x ) : nCkSectn ( nCkT_depT T ).
Proof.
  revert n T X.
  induction k.
  intros.
    simpl. apply X.
  intros.
    simpl.
    apply lS_depS.
    destruct n. intros [ _ []].
    intros [ l ord ].
    set ( approx := 
              IHk l 
                   (fun r : nCk l k => T ( l ; ( r , ord )))
                   (fun r : nCk l k => X ( l ; ( r , ord )))  
                   ).
    rewrite depS_inv.
    auto.
Defined.

Lemma nCkS_depS' { k n : nat } { T : nCkType k n } 
  ( X : forall cx, depT_nCk T cx ) : nCkSectn T.
Proof.
  revert n T X.
  induction k.
  intros.
  apply X. exact tt.
  intros.
  apply lS_depS.
    intro.
    destruct n0 as [l ord].
    simpl.
    simpl in T.
      apply IHk.
      intros.
      exact ( X ( l ; ( cx, ord))).
Defined.

Lemma depS_nCkS { k n : nat } { T : nCkType k n }
  ( X : nCkSectn T ) : forall cx, depT_nCk T cx.
Proof.
  revert n T X.
  induction k.
  intros.
    exact X.
    intros.
      simpl in *.
    destruct cx as [ l [ cx ord ] ].
    apply IHk.
    exact ( depS_lS' X (l ; ord)).
Defined.

Lemma depS_nCkS' { k n : nat } { T : nCk n k -> Type }
  ( X : nCkSectn ( nCkT_depT T ) ) : forall cx, T cx.
Proof.
  revert n T X.
  induction k.
  intros. destruct cx. auto.
  intros.
    destruct cx as [ l [ cx ord ]].
    assert (relevant := 
      fun X => IHk l (fun cy => T ( l ; (cy, ord) )) X cx ).
    apply relevant.
    assert ( guess := depS_lS' X (l ; ord) ). simpl in guess.
      rewrite depS_inv in guess. auto.
Defined.

Lemma nCkMonoType (k n : nat) (T : Type) : nCkType k n.
Proof.
  apply nCkT_depT.
  intro. exact T.
Defined.

Definition nCkList k n T := nCkSectn (nCkMonoType k n T).

Definition nCkKonst k n { T } (t : T) : nCkList k n T.
Proof.
  apply nCkS_depS.
  intro.
  exact t.
Defined.

Lemma nCkProd { k n : nat } (P Q : nCkType k n) : nCkType k n.
Proof.
  apply nCkT_depT.
  exact ( fun x => (depT_nCk P x * depT_nCk Q x)).
Defined.

Lemma nCkSum { k n : nat } (P Q : nCkType k n) : nCkType k n.
Proof.
  apply nCkT_depT.
  exact ( fun x => (depT_nCk P x) + (depT_nCk Q x)).
Defined.

Lemma nCkMap { k n : nat } (P Q : nCkType k n) : nCkType k n.
Proof.
  apply nCkT_depT.
  exact ( fun x => (depT_nCk P x) -> (depT_nCk Q x)).
Defined. *)

Lemma nCkApply { k n : nat } ( P Q : Type ) :
  nCkList P k n -> (nCkList ( P -> Q) k n) -> nCkList Q k n.
Proof.
  intros.
  apply list_fun.
  exact (fun cx => (fun_list X0 cx) (fun_list X cx)).  
Defined.

Lemma tauto  k l : nCkList (nCk l k) k l.
Proof.
  apply list_fun.
  auto.
Defined.

Lemma nCkSubdiv { k } ( l : nat) { n } { T : Type } :
  nCkList T k n -> ( nCkList (nCkList T k l ) l n  ).
Proof.
  intro.
  apply list_fun.
  intros cx.
  apply list_fun.
  intro cy.
  exact ( fun_list X (nCkCompose cx cy)).
Defined.

Lemma nCkEqn { k l n } { T : Type } ( P : nCkList T k n ) :
  forall cx, forall cy, 
    fun_list (fun_list (nCkSubdiv l P) cx) cy = fun_list P (nCkCompose cx cy).
Proof.
  intros.
  unfold nCkSubdiv.
  rewrite fl_inv. rewrite fl_inv. auto.
Defined.

Lemma nCkLEqn { k n } { T : Type } ( p q : nCkList T k n ) :
  (fun_list p == fun_list q) -> p = q.
Proof.
  revert n T p q.
  induction k.
  intros.
   exact (X tt).
  intros.
   apply listEqn''.
   intros [ l ord ].
   apply IHk.
   intro.
   path_via ( fun_list p ( l ; ( x, ord  )) ).
   path_via ( fun_list q ( l ; ( x, ord ))).
Defined.