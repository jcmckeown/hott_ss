Require Import HoTT.

Fixpoint nCk (n k : nat)  : Type :=
  match n with
 | O => match k with O => Unit
    | S k' => Empty end
 | S n' => 
    match k with O => Unit
    | S k' => ( nCk n' k' ) + ( nCk n' (S k'))
       end end.

Fixpoint nCAll n : nCk n n :=
  match n with
| O => tt
| S n' => inl (nCAll n') end.

Fixpoint nCkType (n k : nat) : Type :=
 let U := Type in
  match n with
  | O => match k with O => U | S k' => Unit end
  | S n' => match k with 
    O => U
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

Definition nCkList A n k := nCkSect (nCkLT A n k).

Fixpoint nCTop  {A : Type} { n : nat } : nCkList A n n -> A :=
  match n with
  | O => fun X => X
  | S n' => fun X : (nCkList A n' n') * (nCkList A n' (S n')) => 
    nCTop (fst X) end.

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

(** this isn't as helpful as it seems ... *)
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

Coercion nCkS_T : nCkType >-> nCkList.

Fixpoint nCkT_S { n k } : nCkList Type n k -> nCkType n k.
Proof.
  destruct n.
    destruct k. intros. exact X.
      intros. exact tt.
    destruct k. intros. exact X.
      intros.
      exact ( nCkT_S _ _ (fst X) , nCkT_S _ _ (snd X)).
Defined.

Fixpoint nckelim { n k } : forall (T : nCkType n k),
  nCkSect T -> nCkSect (nCkT_S (nCkS_T T)).
Proof.
  destruct n.
    destruct k.
      intros. exact X.
      intros. exact tt.
    destruct k.
      intros. exact X.
      intros.
      destruct X as [ Xf Xs ].
      destruct T as [ Tf Ts ].
      split.
        simpl. auto.
        simpl. auto.
Defined.

Fixpoint tKonst_elim { n k }
 : forall T, nCkList T n k -> nCkSect (nCkT_S (nCkKonst T n k)).
Proof.
  destruct n.
    destruct k.
      intros.
      exact X.
      intros. exact tt.
    destruct k.
      intros.
      exact X.
      intros.
      exact ( tKonst_elim _ _ _ (fst X), tKonst_elim _ _ _ (snd X)).
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

Fixpoint nCkAllUnit { n k } :
  forall { A : Type } 
    { y : nCkList A n k },
    nCkSect (nCkT_S (nCkApply (nCkKMap (fun _ => Unit : Type) _ _ ) y )).
Proof.
  intros.
  destruct n ; destruct k ; try exact tt.
  exact (nCkAllUnit _ _ _ (fst y), nCkAllUnit _ _ _ (snd y)).
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

Fixpoint nCkfst { n k } :
  forall { A B : nCkType n k },
  nCkSect ( nCkProd A B ) -> nCkSect A :=
match n with
  | O => match k with
    | O => fun A B s => fst s
    | S k' => fun _ _ _ => tt end
  | S n' =>
    match k with
    | O => fun A B s => fst s
    | S k' => fun A B s => ( nCkfst (fst s), nCkfst (snd s)) end end.

Fixpoint nCksnd { n k } :
  forall { A B : nCkType n k },
  nCkSect ( nCkProd A B ) -> nCkSect B :=
match n with
  | O => match k with
    | O => fun A B s => snd s
    | S k' => fun _ _ _ => tt end
  | S n' =>
    match k with
    | O => fun A B s => snd s
    | S k' => fun A B s => ( nCksnd (fst s), nCksnd (snd s)) end end.

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

Fixpoint nCkLfst { A B : Type } { n k } :
  nCkList (A * B) n k -> nCkList A n k :=
match n with
  | O => match k with
    | O => fst
    | S k' => fun _ => tt end
  | S n' => match k with
    | O => fst
    | S k' => fun W : nCkList (A * B) (S n') (S k')
     => (nCkLfst (fst W), nCkLfst (snd W)) end end.

Fixpoint nCkLsnd { A B : Type } { n k } :
  nCkList (A * B) n k -> nCkList B n k :=
match n with
  | O => match k with
    | O => snd
    | S k' => fun _ => tt end
  | S n' => match k with
    | O => snd
    | S k' => fun W : nCkList (A * B) (S n') (S k')
     => (nCkLsnd (fst W), nCkLsnd (snd W)) end end.

Fixpoint nCkMPair { A : Type } { f g : A -> Type } { n k }:
 forall ( a : nCkList A n k ),
  nCkSect (nCkT_S (nCkApply (nCkKMap f n k) a )) ->
    nCkSect (nCkT_S (nCkApply (nCkKMap g n k) a )) -> 
      nCkSect (nCkT_S (nCkApply (nCkKMap (fun z => (f z) * (g z)) n k) a)).
Proof.
  intros a fs gs.
  destruct n.
    destruct k.
      exact ( fs, gs).
      exact tt.
    destruct k.
      exact ( fs, gs).
      exact ( nCkMPair _ _ _ _ _ (fst a) (fst fs) (fst gs),
              nCkMPair _ _ _ _ _ (snd a) (snd fs) (snd gs)).
Defined.

Fixpoint nCkMCompose {A B: Type} (f: B -> Type) (g : A -> B ) {n k} :
  forall (a : nCkList A n k) ,
    nCkSect (nCkT_S (nCkApply (nCkKMap (f o g) _ _) a)) ->
  nCkSect (nCkT_S (nCkApply (nCkKMap f _ _) (nCkApply (nCkKMap g _ _) a))).
Proof.
  intros.
  destruct n.
    destruct k.
      exact X.
      exact tt.
    destruct k.
      exact X.
  destruct X.
  split; simpl; auto.
Defined.

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

Fixpoint nCkExistT { n k } :
  forall { A : nCkType n k} 
    { P : nCkSect (nCkMap A (nCkLT Type n k))}
    ( a : nCkSect A ) ( b : nCkSect (nCkT_S (nCkApply P a)) ),
    nCkSect (nCkSig P).
Proof.
  destruct n.
    destruct k.
      intros.
      exists a. exact b.
      intros.
      exact tt.
    destruct k.
      intros.
      exists a. exact b.
      intros.
      exact (nCkExistT _ _ _ _ (fst a) (fst b) ,
             nCkExistT _ _ _ _ (snd a) (snd b)).
Defined.

Fixpoint nCkProj1' { n k } :
  forall { A : nCkType n k} 
    { P : nCkSect (nCkMap A (nCkLT Type n k))},
   nCkSect (nCkSig P) -> nCkSect A :=
match n with
  | O => match k with
    | O => fun A P s => projT1 s 
    | _ => fun _ _ _ => tt end
  | S n' => match k with
    | O => fun A P s => projT1 s
    | S k' => fun A P s => (nCkProj1' (fst s) , nCkProj1' (snd s)) end end.

Fixpoint nCkProj2' { n k } :
  forall {A : nCkType n k} {P : nCkSect (nCkMap A (nCkLT Type _ _))}
    (s : nCkSect (nCkSig P)) ,
      nCkSect (nCkT_S (nCkApply P (nCkProj1' s))).
Proof.
  intros.
  destruct n.
    destruct k.
      exact (projT2 s).
      exact tt.
    destruct k.
      exact (projT2 s).
      exact ( nCkProj2' _ _ (fst A) (fst P) (fst s),
              nCkProj2' _ _ (snd A) (snd P) (snd s)).
Defined.

Fixpoint nCkLExistT { A : Type }{ P : A -> Type } { n k } :
  forall (a : nCkList A n k)
   (b : nCkSect (nCkT_S (nCkApply (nCkKMap P _ _) a) )),
   nCkList (sigT P) n k.
Proof.
  destruct n.
    destruct k.
    intros. exists a. exact b.
    intros. exact tt.
    destruct k.
    intros. exists a. exact b.
    intros.
    exact (nCkLExistT A P _ _ (fst a) (fst b),
          nCkLExistT A P _ _ (snd a) (snd b)).
Defined.

Fixpoint nCkProj1 {n k} :
 nCkList { T : Type & T } n k -> nCkType n k :=
match n with
  | O => 
    match k with 
     | O => fun Tt => projT1 Tt
     | S k' => fun _ => tt end
  | S n' =>
    match k with
     | O => fun Tt => projT1 Tt 
     | S k' => fun Tt =>
      ( nCkProj1 (fst Tt) , nCkProj1 (snd Tt)) end end.

Fixpoint nCkProj2 {n k} :
  forall A : nCkList { T : Type & T } n k,
    nCkSect (nCkProj1 A).
Proof.
  intros.
  destruct n.
    destruct k.
      exact (projT2 A).
      exact tt.
    destruct k.
      exact (projT2 A).
      exact (nCkProj2 _ _ (fst A), nCkProj2 _ _ (snd A)).
Defined.

Fixpoint nCkSkmap_nCkList { A B : Type } {n k} :
  forall {a : nCkList A n k},
    (nCkList B n k) -> nCkSect (nCkT_S (nCkApply (nCkKMap (fun _ : A => B) n k) a)).
Proof.
  intros a b.
  destruct n.
    destruct k.
      exact b.
      exact tt.
    destruct k.
      exact b.
      exact ( nCkSkmap_nCkList A B _ _ (fst a) (fst b), 
              nCkSkmap_nCkList A B _ _ (snd a) (snd b)).
Defined.

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
(*      change (inr (nCkComp ra (nCkComp b c)) = inr (nCk k n) (nCkComp (nCkComp ra b) c)). *)
      refine (ap inr _). apply nCk_assoc.
Defined.

Fixpoint nCkTSubdiv {k} l {m} :
  forall T : nCkType k m,
    nCkList (nCkType l m) k l.
Proof.
  destruct k.
    destruct l.
      destruct m.
        intros. exact T.
        intros. exact tt.
      intros. exact tt.
    intros.
    destruct l.
      destruct m. exact T.
      apply nCkKonst. exact tt.
      destruct m.
        apply nCkKonst. exact T.
        split.
        simpl.
        refine (nCkLPair (nCkTSubdiv _ l _ (fst T)) (nCkTSubdiv _ l _ (snd T))).
        simpl.
        exact (nCkTSubdiv _ (S l) _ (snd T)).
Defined.

Fixpoint nCkSubdiv { A : Type } {k} l { m } :
(nCkList A k m) -> nCkList (nCkList A l m) k l.
Proof.
  intros.
  destruct k.
   destruct m.
    destruct l ; exact (nCkKonst X _ _ ).
    destruct l ; exact tt.
   destruct m.
    destruct l ; exact (nCkKonst X _ _ ).
    destruct l.
     exact tt.
    split. simpl.
    exact ( nCkLPair (nCkSubdiv _ _ l _ (fst X)) (nCkSubdiv _ _ l _ (snd X))).
    exact ( nCkSubdiv _ _ (S l) _ (snd X)).
Defined.

Fixpoint konstIdmap { A : Type }{ n k : nat }:
  forall (a : nCkList A n k),
    a = (nCkApply (nCkKMap idmap _ _ ) a ).
Proof.
  intros.
  destruct n.
    destruct k.
      exact idpath.
      destruct a; exact idpath.
    destruct k.
      exact idpath.
      apply path_prod.
        apply konstIdmap.
        apply konstIdmap.
Defined.

Definition listOfnCkTs { k l m n } :
  nCkList (nCkList Type k l) m n -> nCkList (nCkType k l) m n :=
  nCkApply (nCkKMap nCkT_S m n).

Lemma listOfSects { k l m n } :
  nCkList (nCkList Type k l) m n -> nCkList Type m n.
Proof.
  refine ( nCkApply (nCkKMap _ _ _ )).
  intro.
  exact (nCkSect (nCkT_S X)).
Defined.

Fixpoint listT_of_Sects { k l m n } :
  nCkList (nCkType k l) m n -> nCkType m n.
Proof.
  destruct m.
    destruct n.
      intro.
      exact (nCkSect X).
     intro. exact tt.
    destruct n.
      intro.
      exact (nCkSect X).
      intro.
      exact ( listT_of_Sects _ _ _ _ (fst X) ,
              listT_of_Sects _ _ _ _ (snd X)).
Defined.

Fixpoint lOfSOfNot k l m :
  @nCkSect l m (@listT_of_Sects 0 (S k) l m (nCkKonst tt l m)).
Proof.
  destruct l.
   destruct m; exact tt.
   destruct m. exact tt.
   exact (lOfSOfNot _ _ _, lOfSOfNot _ _ _).
Defined.

(* 
*)

Fixpoint lSOfOne { T } (t :T) k l m : 
  nCkSect (@listT_of_Sects (S m) 0 _ _ (nCkKonst T k l)).
Proof.
  destruct k.
    destruct l. exact t.
      exact tt.
    destruct l.
      exact t.
      exact (lSOfOne T t _ _ _ , lSOfOne T t _ _ _).
Defined.

Fixpoint lSOfPairs { k l m n } :
 forall (A : nCkList (nCkType k l) m n) ( B : nCkList (nCkType k (S l)) m n ),
        nCkSect (nCkMap (nCkProd (listT_of_Sects A) (listT_of_Sects B))
                        (@listT_of_Sects (S k) (S l) m n (nCkLPair A B))).
Proof.
  destruct m.
    destruct n.
      intros.
        exact idmap.
      intros. exact tt.
    destruct n.
      intros.
        exact idmap.
      intros.
      exact ( lSOfPairs _ _ _ _ (fst A) (fst B),
              lSOfPairs _ _ _ _ (snd A) (snd B)).
Defined.

Fixpoint nCkSSubdiv { k } l { m } :  
  forall { T : nCkType k m } ( s : nCkSect T ),
  nCkSect ( listT_of_Sects (nCkTSubdiv l T )).
Proof.
  destruct k.
    destruct l.
      destruct m; intros; exact s.
      destruct m; intros; exact tt.
    destruct l.
      intros. destruct m; simpl. exact s.
        exact tt.
      destruct m.
       intros.
        simpl.
        split.
        refine (lSOfOne s _ _ _).
        refine (lSOfOne s _ _ _).
       intros.
        split.
        refine (nCkApply (lSOfPairs _ _) _).
        apply nCkPair.
          apply nCkSSubdiv. exact (fst s).
          apply nCkSSubdiv. exact (snd s).
          apply nCkSSubdiv. exact (snd s).
Defined.

Fixpoint nCkL_S { k l } :
  forall { A : nCkType k l },
    nCkSect A -> nCkList { T : Type & T } k l.
Proof.
 intros A a.
  destruct k.
    destruct l.
      exists A. exact a.
      exact tt.
    destruct l.
      exists A. exact a.
      exact ( nCkL_S _ _ (fst A) (fst a), nCkL_S _ _ (snd A) (snd a)).
Defined.

Definition nck_alt_ssubdiv { k } l { m } {A : nCkType k m}
  (a : nCkSect A) :=
  nCkSubdiv l ( nCkL_S a ).

Definition nck_alt_sd {k} l { m } { A : nCkType k m }
  (a : nCkSect A) : nCkList (nCkType l m) k l :=
  nCkApply (nCkKMap nCkProj1 _ _) (nck_alt_ssubdiv l a).

(** 
Fixpoint nCk_alt_ssd {k} l {m}:
 forall { A : nCkType k m } 
  (a : nCkSect A),
    nCkSect (listT_of_Sects (nck_alt_sd l a)). 
Proof.
  intros.
  unfold nck_alt_sd.
  destruct k.
    destruct m.
      destruct l.
        exact a.
        exact tt.
      destruct l.
        exact tt.
        exact tt.
    destruct m.
      destruct l.
        exact a.
        refine (nCkApply _ (nCkKonst a _ _ )).
        simpl in *.
        split.
          apply nCk_alt_ssd. **)