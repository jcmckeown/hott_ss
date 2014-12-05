Require Import HoTT
 austere_nCk.

Local Open Scope path_scope.

Fixpoint typeFun { n k : nat } :
  nCkType n k -> (nCk n k) -> Type.
Proof.
  destruct n.
    destruct k.
      intros T cx.
      exact T.
      intros T [].
    destruct k.
      intros T cx.
      exact T.
      intros T cx.
      destruct cx.
        exact (typeFun _ _ (fst T) n0).
        exact (typeFun _ _ (snd T) n0).
Defined.

Fixpoint sectFun { n k : nat } :
  forall {T : nCkType n k},
   nCkSect T ->
    forall cx : nCk n k, typeFun T cx.
Proof.
  intros.
  destruct n.
   destruct k.
    exact X.
    destruct cx.
   destruct k.
    exact X.
    destruct cx.
     exact (sectFun _ _ (fst T) (fst X) n0).
     exact (sectFun _ _ (snd T) (snd X) n0).
Defined.

Fixpoint listFun { A: Type } { n k : nat }:
  nCkList A n k -> nCk n k -> A .
Proof.
  intros a cx.
   destruct n.
    destruct k.
     exact a.
     destruct cx.
    destruct k.
     exact a.
     destruct cx.
     exact (listFun _ _ _ (fst a) n0).
     exact (listFun _ _ _ (snd a) n0).
Defined.

Fixpoint typeEqn { n k : nat } :
  forall A B : nCkType n k,
    (typeFun A == typeFun B) -> A = B.
Proof.
  intros.
  destruct n.
   destruct k.
    exact (X tt).
    destruct A , B ; exact idpath.
   destruct k.
    exact (X tt).
    apply path_prod.
    refine (typeEqn _ _ _ _ (fun x => X (inl x))).
    refine (typeEqn _ _ _ _ (fun x => X (inr x))).
Defined.

Fixpoint sectEqn { n k : nat } : 
  forall T : nCkType n k,
   forall A B : nCkSect T,
    (sectFun A == sectFun B) -> A = B.
Proof.
  intros.
  destruct n.
   destruct k.
    exact (X tt).
    destruct A, B ; exact idpath.
   destruct k.
    exact (X tt).
    apply path_prod.
    exact (sectEqn _ _ _ _ _ (fun x => X (inl x))).
    exact (sectEqn _ _ _ _ _ (fun x => X (inr x))).
Defined.

Fixpoint listEqn { A : Type } { n k : nat } :
  forall a b : nCkList A n k,
    (listFun a == listFun b) ->
     a = b.
Proof.
  intros.
  destruct n.
   destruct k.
    exact (X tt).
    destruct a , b; exact idpath.
   destruct k.
    exact (X tt).
    apply path_prod.
    exact (listEqn _ _ _ _ _ (fun x => X (inl x))).
    exact (listEqn _ _ _ _ _ (fun x => X (inr x))).
Defined.

Fixpoint konstEqn { A : Type } { a : A } { n k : nat } :
 forall cx,
  (listFun (nCkKonst a n k) cx) = a.
Proof.
  intros.
  destruct n.
    destruct k.
      exact idpath.
      destruct cx.
    destruct k.
      exact idpath.
      destruct cx.
      simpl. apply konstEqn.
      simpl. apply konstEqn.
Defined.

Fixpoint kmapEqn { A B : Type } { f : A -> B } { n k : nat } :
  forall { cx } ( a : nCkList A n k ),
    listFun (nCkApply (nCkKMap f _ _) a) cx = f (listFun a cx).
Proof.
  intros.
  destruct n.
    destruct k.
      exact idpath.
      destruct cx.
    destruct k.
      exact idpath.
      destruct cx.
      simpl; apply kmapEqn.
      simpl; apply kmapEqn.
Defined.

Fixpoint fstEqn { A B : Type } { n k : nat } :
  forall {a : nCkList A n k}{b:nCkList B n k},
    fst o (listFun (nCkLPair a b)) == listFun a.
Proof.
  intros.
  intros cx.
  destruct n.
   destruct k.
    exact idpath.
    destruct cx.
   destruct k.
    exact idpath.
    unfold compose.
    destruct cx ; simpl.
    apply fstEqn.
    apply fstEqn.
Defined.

Fixpoint sndEqn { A B : Type } { n k : nat } :
  forall { a : nCkList A n k } { b : nCkList B n k },
    snd o (listFun (nCkLPair a b)) == listFun b.
Proof.
  intros.
  intros cx.
  destruct n.
   destruct k.
    exact idpath.
    destruct cx.
   destruct k.
    exact idpath.
    unfold compose ; destruct cx ; simpl; apply sndEqn.
Defined.

Fixpoint subdivHtp { A : Type } { n k l : nat } :
  forall a : nCkList A n k,
   forall cx, forall cy,
    listFun (listFun (nCkSubdiv l a) cy) cx
      = listFun a (nCkComp cy cx).
Proof.
  intros.
  destruct n, l, k ; try contradiction; try apply idpath.
    destruct cy; apply konstEqn.
    destruct a as [ al ar ]; simpl in al, ar.
    destruct cy as [ ly | ry ].
      destruct cx as [ lx | rx ].
      simpl.
    path_via (listFun (listFun (nCkSubdiv l al) ly) lx).
    refine (ap (fun z => listFun z lx) _ ).
    apply fstEqn.
    simpl.
    path_via (listFun (listFun (nCkSubdiv l ar) ly) rx).
    refine (ap (fun z => listFun z rx) _).
    apply sndEqn. simpl.
    destruct cx as [ lx | rx ] ; simpl.
    exact (subdivHtp _ n (S k) (S l) ar (inl lx) ry).
    exact (subdivHtp _ n (S k) (S l) ar (inr rx) ry).
Defined.

Lemma subdivEqn { A : Type } { n k l m : nat } :
 forall a : nCkList A n m,
  nCkSubdiv k (nCkSubdiv l a) =
   nCkApply (nCkKMap (nCkSubdiv l) _ _ ) (nCkSubdiv k a).
Proof.
  intros.
  apply listEqn.
  intro cx.
  apply listEqn.
  intro cy.
  apply listEqn.
  intro cz.
  path_via 
    (listFun a (nCkComp (nCkComp cx cy) cz)).
  path_via
    (listFun (listFun (nCkSubdiv l a) (nCkComp cx cy)) cz).
  refine ( ap (fun z => listFun z cz) _ ).
  apply subdivHtp.
  apply subdivHtp.
  path_via
    (listFun (listFun 
      ((nCkSubdiv l) (listFun (nCkSubdiv k a) cx)) cy) cz).
  path_via
    (listFun (listFun (nCkSubdiv k a) cx) (nCkComp cy cz)).
  path_via 
    (listFun a (nCkComp cx (nCkComp cy cz))).
  apply ap.
  refine ((nCk_assoc _ _ _) ^).
  refine ((subdivHtp _ _ _) ^).
  refine ((subdivHtp _ _ _) ^).
  refine ( ap (fun z =>  (listFun z cz)) _ ).
  refine ( ap (fun z => listFun z cy) _).
  refine ( (kmapEqn _ )^ ).
Defined.