Require Import
 FunctionRels
 adhesives.

Record Adjacency : Type := {
  adj_Names : nat -> Type;
  adj_Rels : adhesive adj_Names
  }.


Definition frame (A : Adjacency) (n k : nat) :=
  { 
    facets : lSect (blobList (adj_Names A) n (S k))
      & 
      lSect (gluetype _ (adj_Rels A) facets) }.

Definition Cell (A : Adjacency) (n : nat) :=
  frame A n n.

Definition topFacet (A : Adjacency) (n : nat) (C : Cell A n) : 
  adj_Names A n := nCTop (fst (C .1)).

(*
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
*)

(*
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
*)

Lemma fskel { A : Adjacency } n k l :
  forall (C : frame A n k),
    nCkList (frame A l k) n l.
Proof.
  intros.
  refine 
    (nCkLExistT (subdivided_blob_list l (C.1)) _).
  assert ( ans := glue_from_glue _ l C.2 ).
  unfold partitionSubdivided in ans.
  apply sect_ts_forall.
  intro.
  assert ( help :=
    let ( _ , hlp ) :=
      sect_ts_forall lSect 
        (nCkApply _ _) in hlp ans cx).
  apply lf_comp. auto.
Defined.

Fixpoint boundary (A : Adjacency) (n : nat) (C : Cell A (S n)) :
  nCkList (Cell A n) (S n) n.
Proof.
  set ( R := fskel _ _ n C ).
  refine ( nCkApply (nCkKMap _ _ _ ) R ).
  intros.
  destruct X as [ fs gs ].
  exists (snd fs).
  exact (snd gs).
Defined.

