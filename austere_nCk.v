Require Import HoTT.

Fixpoint nCk (n k : nat)  : Type :=
  match n with
 | O => match k with O => Unit
    | S k' => Empty end
 | S n' => 
    match k with O => Unit
    | S k' => ( nCk n' k' ) + ( nCk n' (S k'))
       end end.

Fixpoint nCkType (n k : nat) : Type :=
  match n with
  | O => match k with O => Type | S k' => Unit end
  | S n' => match k with 
    O => Type
    | S k' => ( nCkType n' k' ) * ( nCkType n' (S k')) end end.

Fixpoint nCkSect { n k : nat } :
  nCkType n k -> Type :=
  match n with 
  | O => match k return nCkType 0 k -> Type with O => 
    fun T : Type => T
    | S k' => fun _ => Unit end
  | S n' => match k return nCkType (S n') k -> Type with O => 
    fun T : Type => T
    | S k' => fun T : ( nCkType n' k' ) * ( nCkType n' (S k')) =>
      ( nCkSect (fst T)) * (nCkSect (snd T)) end end.

Fixpoint nCkLT (A : Type) (n k : nat) :
  nCkType n k :=
match n with
 | O => match k return nCkType 0 k with
  | O => A
  | S k => tt end
 | S n' => match k return nCkType (S n') k with
  | O => A
  | S k' => ((nCkLT A n' k'), (nCkLT A n' (S k'))) end end.

Fixpoint nCk_monOp (W : Type -> Type) { n k : nat } :
 nCkType n k -> nCkType n k :=
match n with
  | O => match k return (nCkType 0 k -> nCkType 0 k) with
    | O => fun T : Type => W T
    | S k' => fun _ => tt end
  | S n' => match k return (nCkType (S n') k -> nCkType (S n') k) with
    | O => fun T : Type => W T
    | S n' => fun T =>
      ( nCk_monOp W (fst T) , nCk_monOp W (snd T) ) end end.

Fixpoint nCk_pairOp (W : Type -> Type -> Type) { n k : nat } :
 nCkType n k -> nCkType n k -> nCkType n k :=
match n return nCkType n k -> nCkType n k -> nCkType n k with
 | O => match k with
  | O => fun A B : Type => (W A B)
  | S k' => fun _ _ => tt end
 | S n' => match k with
  | O => fun A B => (W A B)
  | S k' => fun A B => 
    (nCk_pairOp W (fst A) (fst B), nCk_pairOp W (snd A) (snd B)) end end.

Definition nCkProd { n k : nat } : nCkType n k -> nCkType n k -> nCkType n k :=
  nCk_pairOp prod.

Definition nCkSum { n k : nat } : nCkType n k -> nCkType n k -> nCkType n k :=
  nCk_pairOp sum.

Definition nCkMap { n k : nat } : nCkType n k -> nCkType n k -> nCkType n k :=
  nCk_pairOp (fun A B => A -> B).

(** 
come to sections of things, we probably want eight or so operations
Type -> Type -> Type
Type -> Type -> Sectn A (um... I don't think there are many of these... )
Type -> Sectn A -> Type 
Type -> Sectn A -> Sectn B (or these... )
Sectn A -> Sectn B -> Type
Sectn A -> Sectn B -> Sectn C (but this looks natural-er).
*)

Notation nCkList A n k := (nCkSect (nCkLT A n k)).

Fixpoint nCkKonst {A : Type} (a : A) (n k : nat) : nCkList A n k :=
  match n with
  | O => match k with
    | O => a
    | S k' => tt end
  | S n' => match k with
    | O => a
    | S k' => ( nCkKonst a n' k', nCkKonst a n' (S k')) end end.

Fixpoint nCkKMap { A B : Type } (f : A -> B ) (n k : nat) :
  nCkSect (nCkMap (nCkLT A n k) (nCkLT B n k)).
Proof.
  destruct n.
    destruct k.
      exact f.
      exact tt.
    destruct k.
      exact f.
      exact (nCkKMap _ _ f n k , nCkKMap _ _ f n (S k)).
Defined.

Fixpoint nCk_ST { n k } { struct n } : nCkList Type n k = nCkType n k.
Proof.
  destruct n.
  destruct k.
    exact idpath.
    exact idpath. 
  destruct k.
    exact idpath.
    simpl.
  refine (@ap _ _ (fun A : Type * Type => (fst A * snd A)) 
    (nCkList Type n k , nCkList Type n (S k)) (nCkType n k, nCkType n (S k))
    _
   ).
   apply path_prod.
   apply nCk_ST.
   apply nCk_ST.
Defined.

(** Now, what to do... *)

Fixpoint nCkS_T { n k } : nCkType n k -> nCkList Type n k.
Proof.
  destruct n.
    destruct k.
    auto.
  intro. apply tt.
    destruct k.
    auto.
    intros [ fs sn ].
    exact ( nCkS_T _ _ fs , nCkS_T _ _ sn).
Defined.

(** Vexing point: nCkS_T and nCkT_S reduce to the identity map on 
  identical types ; but proving this is probably impossible,
  in that there isn't a bounded computation that always says the
  rith thing.
  similarly, nCk_ST is idpath in all (reduced) cases *)

Coercion nCkS_T : nCkType >-> nCkSect.

Fixpoint nCkSig {n k} : 
  forall {A : nCkType n k} 
  (P : nCkSect (nCkMap A (nCkLT Type n k))), nCkType n k.
Proof.
  destruct n.
    intros.
    destruct k.
      exact (sigT P).
    exact tt.
    destruct k.
      intros.
      exact (sigT P).
    intros.
      exact ( nCkSig _ _ (fst A)(fst P),
         nCkSig _ _ (snd A)(snd P)).
Defined.

Fixpoint nCkApply { n k } :
  forall { A B : nCkType n k} ,
  (nCkSect (nCkMap A B)) -> (nCkSect A) -> (nCkSect B).
Proof.
  destruct n.
    destruct k.
      intros A B f a.
      exact (f a).
      intros _ B _ _. exact tt.
    destruct k.
      intros A B f a.
      exact (f a).
      intros A B f a.
      exact ( nCkApply _ _ _ _ (fst f) (fst a) , 
        nCkApply _ _ _ _ (snd f) (snd a)).
Defined.

Fixpoint nCkPair { n k } :
  forall { A B : nCkType n k },
   nCkSect A -> nCkSect B -> nCkSect (nCkProd A B) :=
match n with
  | O => match k with
    | O => fun A B a b => (a,b)
    | S k' => fun _ _ _ _ => tt end
  | S n' =>
    match k with
    | O => fun A B a b => (a,b)
    | S k' =>
      fun A B a b =>
      (nCkPair (fst a) (fst b), nCkPair (snd a) (snd b)) end end.

Fixpoint nCkLPair {A B : Type} { n k } : 
  nCkList A n k -> nCkList B n k -> nCkList (A * B) n k :=
match n with
  | O => match k with
    | O => fun (a : A) (b : B) => (a,b)
    | S k' => fun _ _ => tt end
  | S n' =>
    match k with
    | O => fun a b => (a,b)
    | S k' =>
      fun a b =>
      (nCkLPair (fst a) (fst b), nCkLPair (snd a) (snd b)) end end.

Fixpoint tauto (n k : nat) :
  nCkList (nCk n k) n k.
Proof.
  destruct n.
    destruct k.
      exact tt.
      exact tt.
    destruct k.
      exact tt.
    refine ( nCkApply (nCkKMap inl n k) (tauto n k),
          nCkApply (nCkKMap inr n (S k)) (tauto n (S k))).
Defined.

Fixpoint nCkComp { k l m } : nCk k l -> nCk l m -> nCk k m.
Proof.
  destruct k.
  destruct l.
    exact (fun _ => fun x => x).
    intros [].
  destruct l.
    destruct m.
    exact (fun _ => fun _ => tt).
    intros _ [].
  intros [ linx | rechts ].
    destruct m.
    exact (fun _ => tt).
   intros [ port | starb ].
    left. exact (nCkComp _ _ _ linx port).
    right. exact (nCkComp _ _ _ linx starb).
   destruct m.
    exact (fun _ => tt).
    intro oder. right.
    exact (nCkComp _ _ _ rechts oder).
Defined.

 (* the table 
  X  |  l w     | r w'
 --------------------------
l v  | l (w.v)  | r (w'.lv)
r v' | r (w.v') | r (w'.rv')
*)

Fixpoint nCk_assoc { k l m n } { struct k}:
  forall (a : nCk k l) (b : nCk l m) (c : nCk m n),
  nCkComp a (nCkComp b c) = nCkComp (nCkComp a b) c.
Proof.
  destruct k.
    destruct l, m ; try contradiction.
      intros; apply idpath.
    destruct l.
      destruct m, n; try contradiction.
      intros; apply idpath.
    intros [ la | ra ].
      destruct m , n; try contradiction; intros; try apply idpath.
      destruct b. apply idpath. apply idpath.
      destruct b. destruct c. simpl. apply ap. auto.
                simpl. apply ap. auto.
                  destruct c. simpl. apply ap. auto.
                  simpl. apply ap. auto.
      destruct m, n; try contradiction. intros; apply idpath.
        intros; apply idpath.
      intros.
      change (inr (nCkComp ra (nCkComp b c)) = inr (nCk k n) (nCkComp (nCkComp ra b) c)).
      apply ap. apply nCk_assoc.
Defined.

Fixpoint nCkLSubdiv {A : Type} { k } l { m } :
  (nCkList A k m) -> nCkList (nCkList A k l) l m.
Proof.
  destruct k.
    destruct l.
     destruct m.
       intros. exact X.
       intros. exact tt.
     intros. apply nCkKonst. exact tt.
   intros.
    destruct l.
     destruct m. exact X.
     exact tt.
    destruct m.
     apply nCkKonst. apply nCkKonst. exact X.
     split.
      refine (nCkLPair (nCkLSubdiv A k l m (fst X)) (fst (nCkLSubdiv A k (S l) _ (snd X)))).
      refine (nCkLPair (nCkLSubdiv _ _ l _ (snd X)) (snd (nCkLSubdiv _ _ (S l) _ (snd X)))).
Defined.

Fixpoint nCkRSubdivide { A : Type } {k} l { m } :
  (nCkList A k m) -> nCkList (nCkList A l m) k l.
Proof.
  destruct k.
    destruct l.
     destruct m.
       intros. exact X.
       intros. exact tt.
     intros. exact tt.
   intros.
    destruct l.
     destruct m. exact X.
     apply nCkKonst. exact tt.
    destruct m.
     apply nCkKonst. exact X.
    split.
     simpl.
     refine (nCkLPair (nCkRSubdivide _ _ l _ (fst X)) (nCkRSubdivide _ _ l _ (snd X))).
     simpl.
     exact (nCkRSubdivide _ _ (S l) _ (snd X)).
Defined.

