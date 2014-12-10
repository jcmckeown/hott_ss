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

Fixpoint konstEqn { A : Type }(P : A -> Type){ a : A } { n k : nat } :
 forall cx,
  P (listFun (nCkKonst a n k) cx) <-> P a.
Proof.
  intros.
  destruct n.
    destruct k.
      ideqv.
      destruct cx.
    destruct k.
      ideqv.
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

Fixpoint funType { n k } :
  (nCk n k -> Type) -> nCkType n k.
Proof.
  intros.
  destruct n.
    destruct k.
      exact (X tt).
      exact tt.
    destruct k.
      exact (X tt).
      exact (funType n k (fun cx => X (inl cx)),
              funType n (S k) (fun cx => X (inr cx))).
Defined.

Fixpoint funList {A : Type} {n k} :
  (nCk n k -> A) -> nCkList A n k.
Proof.
  intros.
  destruct n.
    destruct k.
      exact (X tt).
      exact tt.
    destruct k.
      exact (X tt).
      exact (funList A n k (fun cx => X (inl cx)),
             funList A n (S k) (fun cx => X (inr cx))).
Defined.

Fixpoint sectFunType { n k } :
  forall (T : (nCk n k -> Type)),
    (forall cx, T cx) -> nCkSect (funType T).
Proof.
  intros.
  destruct n.
    destruct k.
      exact (X tt).
      exact tt.
    destruct k.
      exact (X tt).
      exact (sectFunType n k _ (fun cx => X (inl cx)),
             sectFunType n (S k) _ (fun cx => X (inr cx))).
Defined.

Fixpoint sectTypeFun { n k } :
  forall (T : nCkType n k),
    (forall cx, typeFun T cx) -> nCkSect T.
Proof.
  intros.
  destruct n.
    destruct k.
      exact (X tt).
      exact tt.
    destruct k.
      exact (X tt).
      exact (sectTypeFun n k (fst T) (fun cx => X (inl cx)),
            sectTypeFun n (S k) (snd T) (fun cx => X (inr cx))).
Defined.

Fixpoint sect_ts_forall {A : Type }(f : A -> Type){ n k } :
  forall (a : nCkList A n k),
    (forall cx, f (listFun a cx)) <->
      nCkSect (nCkT_S (nCkApply (nCkKMap f _ _ ) a)).
Proof.
  intros.
  destruct n.
    destruct k.
      split; intros.
        exact (X tt).
        exact X.
      split; intros.
        exact tt.
        destruct cx.
    destruct k.
     split; intros.
      exact (X tt).
      exact X.
     split; intros.
      split.
       simpl. apply sect_ts_forall.
        exact (fun cx => X (inl cx)).
       simpl. apply sect_ts_forall.
        exact (fun cx => X (inr cx)).
      destruct cx as [ lx | rx ].
        apply (sect_ts_forall A f n k). exact (fst X).
        apply (sect_ts_forall A f n (S k)). exact (snd X).
Defined.

Fixpoint listFun_pairs { A B : Type } ( f : A * B -> Type )
  { n k : nat } :
forall (a : nCkList A n k) (b : nCkList B n k) (cx : nCk n k),
  f (listFun a cx, listFun b cx)
    <->
  f (listFun (nCkLPair a b) cx).
Proof.
  intros.
  destruct n.
    destruct k.
      ideqv.
      destruct cx.
    destruct k.
      ideqv.
      destruct cx as [ lx | rx ].
      exact ( listFun_pairs A B f n k (fst a) (fst b) lx ).
      exact ( listFun_pairs A B f n (S k) (snd a) (snd b) rx ).
Defined.

Fixpoint lf_fst { A B : Type } ( f : A -> Type )
 { n k : nat } :
forall (a : nCkList A n k) (b : nCkList B n k) (cx: _),
  f ( listFun a cx ) <-> f ( fst (listFun (nCkLPair a b) cx)).
Proof.
  intros.
  destruct n.
    destruct k.
      ideqv.
      destruct cx.
    destruct k.
      ideqv.
      destruct cx as [ lx | rx ].
        exact (lf_fst _ _ _ n k (fst a) _ lx).
        exact (lf_fst _ _ _ n (S k) (snd a) _ rx).
Defined.

Fixpoint lf_snd { A B : Type } ( f : B -> Type ) 
 {n k : nat } : 
forall (a : nCkList A n k) (b : nCkList B n k) (cx: _),
  f ( listFun b cx ) <-> f ( snd (listFun (nCkLPair a b) cx)).
Proof.
  intros.
  destruct n.
    destruct k.
      ideqv.
      destruct cx.
    destruct k.
      ideqv.
      destruct cx as [ lx | rx ].
      exact (lf_snd _ _ _ n k _ (fst b) lx).
      exact (lf_snd _ _ _ n (S k) _ (snd b) rx).
Defined.


Fixpoint lf_comp { A B : Type } (f : A -> B) (P : B -> Type) { n k } :
forall (a : nCkList A n k) (cx : _),
P (listFun (nCkApply (nCkKMap f _ _ ) a) cx) <-> P (f (listFun a cx)).
Proof.
  intros.
  destruct n.
    destruct k.
      ideqv.
      destruct cx.
    destruct k.
      ideqv.
      destruct cx as [ lx | rx ].
    exact (lf_comp A B f P n k 
            (fst a) lx).
    exact (lf_comp A B f P n (S k)
            (snd a) rx).
Defined.

Fixpoint fun_tf_forall{A : Type} (f : A -> Type) { n k : nat } : 
    forall (a : nCkList A n k),
  forall cx, typeFun (nCkT_S (nCkApply (nCkKMap f _ _) a)) cx 
  <->
   f ( listFun a cx ).
Proof.
  intros.
  destruct n.
    destruct k.
      ideqv.
      destruct cx.
    destruct k.
      ideqv.
    destruct cx as [ lx | rx ].
      exact (fun_tf_forall A f n k (fst a) lx).
      exact (fun_tf_forall A f n (S k) (snd a) rx).
Defined.

Fixpoint subdivHtp { A : Type }(P : A -> Type) { n k l : nat } :
  forall a : nCkList A n k,
   forall cx : nCk l k, forall cy : nCk n l,
    P (listFun (listFun (nCkSubdiv l a) cy) cx)
      <-> P (listFun a (nCkComp cy cx)).
Proof.
  intros.
  destruct n, l, k ; try contradiction; try ideqv.
    simpl.
      clear.
     destruct cy ;
      apply konstEqn.
    destruct a as [ al ar ]; simpl in al, ar.
    destruct cy as [ ly | ry ].
      destruct cx as [ lx | rx ].
       simpl.
       apply subdivHtp.
       apply (lf_fst (fun z => P (listFun z lx) <-> _ )).
        ideqv.
       simpl.
       apply subdivHtp.
       apply (lf_snd (fun z => 
          P (listFun z rx) <-> _ )). ideqv.
    destruct cx as [ lx | rx ] ; simpl.
    exact (subdivHtp _ _ n (S k) (S l) ar (inl lx) ry).
    exact (subdivHtp _ _ n (S k) (S l) ar (inr rx) ry).
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
  exact idpath.
  apply subdivHtp. exact idpath.
  path_via
    (listFun (listFun 
      ((nCkSubdiv l) (listFun (nCkSubdiv k a) cx)) cy) cz).
  path_via
    (listFun (listFun (nCkSubdiv k a) cx) (nCkComp cy cz)).
  path_via 
    (listFun a (nCkComp cx (nCkComp cy cz))).
  apply ap.
  apply nCk_assoc. exact idpath.
  apply subdivHtp. exact idpath.
  apply (subdivHtp _ (listFun (nCkSubdiv k a) cx)).
    exact idpath.
  refine ( ap (fun z =>  (listFun z cz)) _ ).
  refine ( ap (fun z => listFun z cy) _).
  refine ( (kmapEqn _ )^ ).
Defined.
