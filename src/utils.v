(** This file holds many kinds of miscellaneous that are used in most other
    files. *)

Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.Eqdep_dec.
Require Export Coq.Program.Basics.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.
Require Export Ring.
Require Export Coq.Classes.Morphisms.
Require Export ennr.

Export EqNotations.
Open Scope ennr.

Notation "f ∘ g" := (compose f g).

(** * Additions to [option]

    Add some functions and notations inspired by Haskell's Maybe *)
Definition fromOption {A} (d : A) (opt : option A) : A :=
  match opt with
  | Some a' => a'
  | None => d
  end.

Definition option0 : option R+ -> R+ := fromOption 0.

Notation "f <$> x" := (option_map f x) (at level 20, left associativity).
Definition option_ap {A B} (o_f : option (A -> B)) : option A -> option B :=
  fun a =>
    match o_f with
    | Some f => f <$> a
    | None => None
    end.
Notation "f <*> x" := (option_ap f x) (at level 20).

Definition option_bind {A B} (t : option A) (f : A -> option B) : option B :=
  match t with
  | Some a => f a
  | None => None
  end.

Definition id {A} := @Datatypes.id A.

(** [dep_destruct] crudely extends the [dependent destruction] tactic to
    destruct multiple variables at once. *)
Ltac dep_destruct xs :=
  lazymatch xs with
  | (?a, ?b) => dep_destruct a; dependent destruction b
  | ?a => dependent destruction a
  end.

(** [econtradict] is like [contradict], but with more existentials. *)
Ltac econtradict e := exfalso; eapply e; repeat econstructor; eauto.

(** This instance uses functional extensionality to allow the [setoid_rewrite]
    tactic to rewrite terms under a lambda.

    Mostly taken from
    #<a href="http://coq-club.inria.narkive.com/PbdQR4E7/rewriting-under-abstractions">
    http://coq-club.inria.narkive.com/PbdQR4E7/rewriting-under-abstractions
    </a># *)

Instance functional_ext_rewriting {A B C} (f : (A -> B) -> C) :
  Proper (pointwise_relation A eq ==> eq) f.
Proof.
  intros x y Hxy.
  pose proof functional_extensionality x y Hxy.
  subst.
  reflexivity.
Qed.

Instance functional_ext_rewriting2 {A B C D} (f : A -> (B -> C) -> D) :
  Proper (eq ==> pointwise_relation B eq ==> eq) f.
Proof.
  intros x y Hxy.
  intros z w Hzw.
  rewrite (functional_extensionality z w Hzw).
  subst.
  reflexivity.
Qed.

Instance refl_respectful {A B RA RB}
         `(sa : subrelation A RA eq)
         `(sb : subrelation B eq RB)
  : Reflexive (RA ++> RB)%signature.
Proof.
  intros f x x' Hxx'.
  apply sb.
  f_equal.
  apply sa; auto.
Qed.

Instance subrel_eq_respect {A B RA RB}
         `(sa : subrelation A RA eq)
         `(sb : subrelation B eq RB)
  : subrelation eq (respectful RA RB).
Proof.
  intros f g Hfg.
  intros a a' Raa'.
  apply sb.
  f_equal.
  apply sa; auto.
Qed.

Instance pointwise_eq_ext {A B RB}
         `(sb : subrelation B RB (@eq B))
  : subrelation (pointwise_relation A RB) eq.
Proof.
  intros f g Hfg.
  extensionality x.
  apply sb.
  apply (Hfg x).
Qed.

Instance eq_pointwise {A B RB}
         `(sb : subrelation B (@eq B) RB) :
  subrelation eq (pointwise_relation A RB).
Proof.
  intros f g Hfg x.
  apply sb.
  subst.
  reflexivity.
Qed.
