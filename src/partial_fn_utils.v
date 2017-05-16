Require Import Coq.Reals.Reals.
Require Import Coq.Sets.Ensembles.

Definition image {A B} (f : A -> B) (aset : A -> Prop) : (B -> Prop) :=
  fun b => exists a, aset a /\ f a = b.

Definition imageb {A B} (f : A -> B) (dec_set : A -> bool) : (B -> Prop) :=
  fun b => exists a, dec_set a = true /\ f a = b.

Section PartialBijections.
  Context
    {X Y : Type}
    (dom : X -> bool)
    (f : X -> Y)
    (finv : Y -> X).

  Definition partial_bijection : Prop :=
    forall x, dom x = true -> finv (f x) = x.
End PartialBijections.

Definition partially_derivable (dom : R -> bool) (f : R -> R) :=
  forall x, dom x = true -> derivable_pt f x.

Definition partially_derive {dom f} (pr : partially_derivable dom f) (x : R) : R :=
  (if dom x as b return (dom x = b -> R)
   then fun H => proj1_sig (pr x H)
   else fun _ => R0) eq_refl.