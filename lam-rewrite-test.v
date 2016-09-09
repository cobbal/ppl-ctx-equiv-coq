Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Instance i0 {A B C} (f : (A -> B) -> C) :
  Proper (pointwise_relation A eq ==> eq) f.
Proof.
  intros x y Hxy.
  pose proof functional_extensionality x y Hxy.
  subst.
  reflexivity.
Qed.

Instance i1 {A B} (a b : A -> B) (f : ((B -> A) -> B) -> nat) :
  Proper (@eq A ==> @eq A ==> Basics.flip Basics.impl) (@eq A).
Proof.
  intuition.
Qed.

Lemma test_rewrite {A B} (a b : A -> B) (f : ((B -> A) -> B) -> nat) (z : B) :
  (forall xz, a xz = b xz) ->
  f (fun (x : B -> A) => a (x z)) = f (fun x => b (x z)).
Proof.
  intros.
  setoid_rewrite H.
  reflexivity.
  apply i0; auto.
  compute.
  intros.
  rewrite H.
  auto.
Qed.



Print Assumptions test_rewrite.
