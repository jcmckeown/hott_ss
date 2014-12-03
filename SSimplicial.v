Require Import
 HoTT
 Nat
 generalLists
 FunctionRels.

(** I wonder what happens if we don't bother with lList? *)

Fixpoint ListOfNcKS
  ( A : nat -> Type )
  ( n k : nat ) : Type :=
match k with
  | O => Unit
  | S k' => nCkList (A k') n k' * ListOfNcKS A n k' end.

Fixpoint baseColor (A : nat -> Type) (n k : nat) :
 (ListOfNcKS A n (S k)) -> (A 0).
Proof.
  destruct k.
   intros.
    destruct n.
      exact ( fst X ).
      exact ( fst X ).
   intros.
    exact (baseColor A n k (snd X)).
Defined.

Fixpoint listFromColor (A : nat -> Type) (n : nat) :
  (A 0) -> ListOfNcKS A 0 (S n).
Proof.
  destruct n.
  intros. exact (X , tt).
  intros.
  split. exact tt.
  auto.
Defined.

Fixpoint ListOfSubdivs 
  ( A : nat -> Type )
  ( k l m : nat )
  : (ListOfNcKS A m k) -> nCkList (ListOfNcKS A l k) m l.
Proof.
  destruct m.
    destruct l.
      intros.
        destruct k.
          exact X.
          exact X.
      intros.
        exact tt.
    destruct l.
      intros.
        destruct k.
          exact X.
          apply listFromColor. exact (baseColor _ _ _ X).
      intros.
      destruct k.
        simpl ListOfNcKS. apply nCkKonst. exact tt.
        destruct X.
        apply nCkLPair.
        refine ( nCkSubdiv _ n ).
        auto.
Defined.

Record Adjacency : Type := {
  adj_Names : nat -> Type;
  adj_Rels : 
    forall n, ((adj_Names (S n)) * (nCkList (adj_Names n) (S n) n)) -> Type
  }.

Fixpoint glueType (A : Adjacency) { k l : nat} :
  (ListOfNcKS (adj_Names A) k (S l)) -> Type.
Proof.
  destruct l.
  intros.
    exact Unit.
  intros.
(*    destruct X as [ X0 [X1 Xrest] ]. *)
    refine ( _ * glueType A _ _ (snd X)).
    refine ( @nCkSect k (S l) (nCkT_S _)).
    refine ( nCkApply (nCkKMap (adj_Rels A l) _ _ ) _).
    apply nCkLPair.
      exact (fst X).
      refine (nCkSubdiv _ (fst (snd X))).
Defined.

Definition frame (A : Adjacency) (n k : nat) :=
  { 
    facets : ListOfNcKS (adj_Names A) n (S k)
      & 
      glueType A facets }.

Definition Cell (A : Adjacency) (n : nat) :=
  frame A n n.

Definition topFacet (A : Adjacency) (n : nat) (C : Cell A n) : 
  adj_Names A n := nCTop (fst (C .1)).

Fixpoint frameFromColor (A : Adjacency) (n : nat) :
  forall a : (adj_Names A) 0,
   glueType A (listFromColor (adj_Names A) n a).
Proof.
  intros.
  destruct n.
    exact tt.
    split.
    exact tt.
    simpl.
    auto.
Defined.

Fixpoint nCkAllUnitSect {A} { n l } :
  forall s : nCkList A n l,
    (nCkSect (nCkT_S (nCkApply (nCkKMap (fun _ : A => Unit : Type) _ _ ) s ))).
Proof.
  intros.
  destruct n.
    destruct l.
      exact tt.
      exact tt.
    destruct l.
      exact tt.
      exact ( nCkAllUnitSect _ _ _ (fst s),
              nCkAllUnitSect _ _ _ (snd s) ).
Defined.

Definition subdiv_step { A : Adjacency }{ n k } l 
    ( C1 : nCkList (adj_Names A (S k)) n (S k) )
    ( C2 : nCkList (adj_Names A k) n k )
    ( gg : nCkSect (nCkT_S (nCkApply (nCkKMap (adj_Rels A k) _ _)
                                              (nCkLPair C1 (nCkSubdiv _ C2)) ) ) )
  := nCkSSubdiv l gg.

Fixpoint layeredSubdivs { A : Adjacency } { n k } (l : nat) :
   forall (fs : ListOfNcKS (adj_Names A) n (S k)), glueType A fs -> Type.
Proof.
    destruct k.
    intros.
      exact Unit.
    intros. simpl in X.
    refine ( _ * _ ).
    exact (nCkSect
            (listT_of_Sects 
              (nCkTSubdiv l 
                (nCkT_S
                   (nCkApply
                           (nCkKMap (adj_Rels A k) n (S k))
                           (nCkLPair (fst fs) 
                                     (nCkSubdiv (S k) (fst (snd  fs)))
                            )
                    )
                 )
               )
             )
          ). (** That ugly thing is exactly the computed return type of subdiv_step. and that's why *)
    exact ( layeredSubdivs A _ _ l (snd fs) (snd X)).
Defined.

Fixpoint raw_fskel { A : Adjacency }{n k} l :
   forall (fs : ListOfNcKS (adj_Names A) n (S k)) (gs : glueType A fs),
     layeredSubdivs l fs gs 
 :=
  match k with
  | O => fun (fs : ListOfNcKS (adj_Names A) n (S O))(gs : glueType A fs) => tt 
  | S k' => fun (fs : ListOfNcKS (adj_Names A) n (S (S k')))
                (gs :  glueType A fs) =>
            ( subdiv_step l (fst fs) (fst (snd fs)) (fst gs) , raw_fskel l (snd fs) (snd gs) ) end.

Lemma e_fskel { A : Adjacency } { n k } l :
  forall (fs : ListOfNcKS (adj_Names A) n (S k))
         (gs : glueType A fs),
    nCkSect (nCkT_S (nCkApply (nCkKMap (fun facets => glueType A facets) n l)
                              ( ListOfSubdivs (adj_Names A) (S k) l n fs ))).
Proof.
  intros.
  assert ( Guide := raw_fskel l fs gs ).
  destruct k.
    destruct l.
      destruct n.
        exact tt.
        exact tt.
      destruct n.
        exact tt.
        split.
        simpl.
          destruct fs.
          apply nCkAllUnitSect.
          apply nCkAllUnitSect.
      destruct n.
        destruct l.
          refine ( tt, _ ).
          simpl. exact (snd gs).
          exact tt.
        destruct l.
          refine (tt, _).
           simpl. apply frameFromColor.
          destruct fs as [ f1a [ f1b fs ] ].
          destruct gs as [ g1 gs ].
          unfold snd in gs.
        destruct Guide as [ Guide1 Guide2 ].
        split.
        simpl.

(** Check nCkSSubdiv (S l) C2ab *)
  
        unfold ListOfSubdivs.
          lazy delta.

Abort.
(*          *)


Lemma fskel { A : Adjacency } n k l :
  forall (C : frame A n k),
    nCkList (frame A l k) n l.
Proof.
  intros.
  refine 
    (nCkLExistT ( ListOfSubdivs _ _ _ _ ( C .1 ) ) _).
  destruct C as [ leaves glue ].
  simpl projT1.
  destruct n.
    destruct l. exact glue. exact tt.
    destruct l. simpl.
      destruct k. exact tt.
        refine ( tt , _ ).
        destruct glue. simpl.
        apply frameFromColor.
      destruct k.
        split. simpl.
        destruct leaves. simpl.
        apply nCkAllUnitSect.
        apply nCkAllUnitSect.
      destruct glue as [ gf gr ].
        set ( helpr := fskel 
      destruct leaves as [ lf lr ].
      destruct gf as [ gf1 gf2 ].
      destruct lf as [ lf1 lf2 ].
      assert ( help1 := nCkSSubdiv l gf1).
      assert ( help2 := nCkSSubdiv (S l) gf2).
    

(* (frame A 0 (S k) ) means ( S k ) layers of 
  ( 0 -choose- l things from (A.1 l) for l ≤ k ), 
  and glue between the layers; this means 0 things from the upper layers
  and one thing from (A.1 0), the unique bottom thing of C ... .  But how to work it... *)
  
(* I think this fragment was lifted from another proof. not sure...

    destruct C as [ facets glue ].
  set ( ff := fun_lS _ facets ).
  set ( gf := fun_lS _ glue ).
  set ( helper :=
    lS_fun (fun z => nCkSubdiv k (ff z)) ).
  set ( helper2 :=
    lS_fun (fun z => nCkSSubdiv k (gf (z.1 ; z.2) ) ) ).
  
  destruct k.
    destruct n.
      exists ( ff ( 0 ; tt ) , tt).
      exact tt.
      exists ( ff ( 0 ; tt ) , tt).
      exact tt.
    destruct n.
      exact tt.
    split.
      simpl.


  intro cx.
exists ( fun k => (fun_list (nCkSubdiv _ (facets k)) cx) ).
intros.
rewrite nCkEqn.
refine ( transport _ _ (glue _ (nCkCompose cx z))).
unfold nCkSubdiv.
repeat progress ( rewrite fl_inv ).
apply nCkLEqn.
intro cz.
repeat progress ( rewrite fl_inv ).
apply ap.
symmetry.
exact (nCkAssoc cx z cz).
Defined.
*)

Fixpoint boundary (A : Adjacency) (n : nat) (C : Cell A (S n)) :
  nCkList (Cell A n) (S n) n.
Proof.
  destruct C as [ facets glue ].
  destruct n.
    exists ( (fun_lS _ facets ( 0 ; tt )) , tt ).
    exact tt.
  
  split.
  
Abort.