Require Import HoTT
 Nat
 ordmap.

Fixpoint lType (l : nat) : Type :=
  match l with
  | 0 => Unit
  | S l' => Type * lType l' end.

Fixpoint lSect { l : nat } : lType l -> Type :=
  match l return (lType l -> Type) 
  with
  | O => fun _ => Unit
  | S l' =>
    fun ( T : Type * lType l' ) =>
      let ( t , T' ) := T in t * lSect T' end.

Fixpoint lT_fun { l : nat } : 
( LT l -> Type ) -> lType l :=
match l return ( LT l -> Type) -> lType l with
 | O => fun _ => tt
 | S l' => fun f : LT (S l') -> Type =>
   ( f ( LT_z _ ) , lT_fun ( f o LT_plus) ) end.

Fixpoint lS_fun { l : nat } :
  forall { T : LT l -> Type }, ( forall z, T z ) ->  lSect (lT_fun T) :=
match l return ( forall T : LT l -> Type, (forall z, T z) -> lSect (lT_fun T) )
 with
 | O => fun _ _ => tt
 | S l' => 
  fun T : (LT (S l') -> Type ) =>
    fun f : forall z, T z =>
     ( f ( LT_z _ ) , lS_fun ( fun r : LT l' => f (LT_plus r) ) ) end.

Fixpoint lS_eqn { l : nat } :
  forall { T : LT l -> Type }, forall {f g : forall z, T z },
   f == g -> ( lS_fun f = lS_fun g ) :=
match l return ( forall { T : LT l -> Type }, forall {f g : forall z, T z },
   f == g -> ( lS_fun f = lS_fun g ) ) with
 | O => fun T f g h => @idpath _ tt
 | S l' => fun T f g h =>
  @path_prod _ _ (lS_fun f) (lS_fun g)
    (h (LT_z _)) (lS_eqn (fun z => h (LT_plus z))) end.

Notation lList T l :=
  (@lSect l (lT_fun (fun _ => T))).

Notation lTKonst a l :=
  ( @lS_fun l ( fun _ => _ ) (fun _ => a) ).

Fixpoint lS_map { l : nat } : 
 forall { U V : LT l -> Type } ( f : forall z, U z -> V z ),
 ( lSect ( lT_fun U ) ) -> ( lSect (lT_fun V) ).
Proof.
  destruct l as [ | l'].
  intros U V f s.
  exact tt.
  intros U V f s.
  destruct s as [ s0 s' ].
  exact ( f _ s0 , lS_map l' _ _ (fun z => f ( LT_plus z)) s' ).
Defined.

