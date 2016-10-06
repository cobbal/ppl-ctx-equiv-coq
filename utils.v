Require Import Basics.
Require Import nnr.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.

Notation "a  '⨉'  b" := (prod a b) (at level 40, left associativity).

Notation "'existsT' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsT'  '/ ' x .. y , '/ ' p ']'")
  : type_scope.

Definition uniqueT {A : Type} (P : A -> Type) (x : A) :=
  P x ⨉ forall x' : A, P x' -> x = x'.

Notation "'existsT' ! x .. y , p" :=
  (sigT (uniqueT (fun x => .. (sigT (uniqueT (fun y => p))) ..)))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' !  '/ ' x .. y , '/ ' p ']'")
    : type_scope.


Definition fromOption {A} (d : A) (opt : option A) : A :=
  match opt with
  | Some a' => a'
  | None => d
  end.

Definition option0 : option R+ -> R+ := fromOption nnr_0.

Notation "f ∘ g" := (compose f g).

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
Notation "f =<< x" := (option_bind x f) (at level 20).
Notation "x >>= f" := (option_bind x f) (at level 20).

Definition id {A} := @Datatypes.id A.

Definition option_join {A} : option (option A) -> option A :=
  fun x => id =<< x.

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

(* setoid rewriting under lambda *)
(* http://coq-club.inria.narkive.com/PbdQR4E7/rewriting-under-abstractions *)
Require Import Setoid Morphisms Program.Syntax.
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