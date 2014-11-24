Require Import HoTT.
Require Import Nat.
Require Import ordmap.
Require Import nCk.

Open Scope path_scope.

Fixpoint lType (l : nat) : Type :=
  match l with
 | O => Unit
 | S l' => Type * (lType l') end.

Lemma lSect {l : nat} (lt : lType l) : Type.
Proof.
  induction l.
  exact Unit.
  destruct lt.
    exact (T * (IHl l0)).
Defined.

Definition LT_plus { l : nat } : LT l -> LT (S l).
Proof.
  intros [ k ordk ].
  exists (S k).
  auto.
Defined.

Definition LT_z (l : nat) : LT (S l) :=
  ( 0 ; tt ).

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
    apply ap. refine ( path_sigma' (lt _) 1 _).
      apply hset_lt.
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
  induction l.
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
      destruct k.
        refine (transport T _ t).
          unfold LT_z. apply ap. apply hset_lt.
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
    refine ( @transport _ ( fun X : (LT_z l = LT_z l)
               => transport P X (p (LT_z l)) = p (LT_z l)) idpath _ _ idpath ).
    apply (hset_decidable dec_eq_mval).
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

Fixpoint nCkType (k n : nat) : Type :=
  match k with
 | O => Type
 | S k' => lSect ( @lT_depT n (compose (nCkType k') idx ) ) end.

Lemma nCkT_depT { k n : nat } : 
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
Defined.

Lemma nCkApply { k n : nat } ( P Q : nCkType k n ) :
  nCkSectn P -> (nCkSectn (nCkMap P Q)) -> nCkSectn Q.
Proof.
  intros.
  apply nCkS_depS'.
  intro.
  set ( help_f := depS_nCkS' X0 cx).
  set ( help_p := depS_nCkS X cx).
  auto.
Defined.

Lemma tauto { k l } : nCkList k l (nCk l k).
Proof.
  apply nCkS_depS.
  auto.
Defined.

Lemma nCkSubdiv { k l n } { T : Type } :
  nCkList k n T -> ( nCkList l n (nCkList k l T ) ).
Proof.
  intro.
  apply nCkS_depS.
  intros.
  apply nCkS_depS.
  intro.
  assert ( ans := depS_nCkS X ( nCkCompose x x0) ).
  unfold nCkMonoType in ans.
    rewrite depT_nCk_inv in ans.
  auto.
Defined.

