Require Import Coq.Logic.Classical.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.RelationClasses.
Require Import Basics.
Require Import Ensembles.

(* Module propifications. *)
  Local Open Scope equiv_scope.

  (* Parameter B : Type. *)
  (* Parameter eqrel : B -> B -> Prop. *)
  (* Parameter eqrel_equiv : Equivalence eqrel. *)

  Record lone B `(Equivalence B) :=
    mk_lone { lone_pred :> B -> Prop;
              lone_unique :
                forall (b0 b1 : B),
                  lone_pred b0 -> lone_pred b1 -> R b0 b1;
            }.
  Arguments mk_lone {_ _ _} _ _.
  Arguments lone_unique {_ _ _} _ _ _ _ _.

  (* Notation  "x  ~+>  y" := (partial_function x y) *)
(*                            (at level 99, right associativity, y at level 200). *)

  Record one B `(Equivalence B) :=
    mk_one' { one_lone :> lone B H;
              one_ex : exists b : B, one_lone b
            }.
  Arguments mk_one' {_ _ _} _ _.
  Arguments one_ex {_ _ _}_.

Definition mk_one {B} `{Equivalence B} (f : B -> Prop) unq ex :=
  mk_one' (mk_lone f unq) ex.

Definition one_equiv B `{Equivalence B} : relation (one B H) :=
  fun o0 o1 =>
    forall b0 b1,
      o0 b0 -> o1 b1 -> R b0 b1.

Lemma one_equiv_refl B `{Equivalence B} : Reflexive (one_equiv B).
Proof.
  unfold Reflexive, one_equiv.
  intro o.
  apply lone_unique.
Qed.

Lemma one_equiv_sym B `{Equivalence B} : Symmetric (one_equiv B).
Proof.
  unfold Symmetric, one_equiv.
  intros.
  symmetry.
  apply H0; auto.
Qed.

Lemma one_equiv_trans B `{Equivalence B} : Transitive (one_equiv B).
Proof.
  intros x y z.
  unfold one_equiv.
  destruct y as [? [y ?]].
  simpl.
  intros.
  rewrite (H0 b0 y); auto.
Qed.

Instance one_equivalence B `{Equivalence B} : Equivalence (one_equiv B) :=
  {
    Equivalence_Reflexive := one_equiv_refl B;
    Equivalence_Symmetric := one_equiv_sym B;
    Equivalence_Transitive := one_equiv_trans B;
  }.

Add Parametric Relation (B : Type) `{Equivalence B} : (one B H) (one_equiv B)
    reflexivity proved by (one_equiv_refl B)
    symmetry proved by (one_equiv_sym B)
    transitivity proved by (one_equiv_trans B)
  as one_equiv_rel.

Program Definition the_one {B} `{Equivalence B} (b : B) : one B H
  := mk_one (R b) _ _.
Next Obligation.
  transitivity b; [symmetry |]; assumption.
Qed.
Next Obligation.
  exists b.
  reflexivity.
Qed.

Definition defined {B} (f : B -> Prop) := exists b, f b.

Definition complete_val {B} `{Equivalence B} (default : B) (f : lone B H) : B -> Prop :=
  fun b =>
    ((f b) \/
     (~defined f /\ R b default)).

Program Definition complete {B} `{Equivalence B} (default : B) (f : lone B H) : one B H
  := mk_one (complete_val default f) _ _.
Next Obligation.
  unfold complete_val in *.
  destruct f as [f ?]; simpl in *.
  destruct (classic (defined f)); try solve [intuition].
  destruct H0, H1; try (contradict H2; eexists; eauto; fail).
  rewrite (proj2 H0), (proj2 H1).
  reflexivity.
Qed.
Next Obligation.
  unfold complete_val.
  destruct (classic (defined f)). {
    destruct H0.
    exists x.
    intuition.
  } {
    exists default.
    intuition.
  }
Qed.

Program Definition lift_lone {A B} `{Equivalence A} `{Equivalence B} (f : A -> B)
  : lone A H -> lone B H0 :=
  fun la =>
    mk_lone (fun b => defined la /\ (forall a, la a -> b = f a)) _.
Next Obligation.
  destruct H1.
  rewrite (H4 x H1).
  rewrite (H3 x H1).
  reflexivity.
Qed.

Program Definition lift_lone2 {A B C}
        `{Equivalence A} `{Equivalence B} `{Equivalence C}
        (f : A -> B -> C) : lone A H -> lone B H0 -> lone C H1 :=
  fun la lb =>
    mk_lone (fun c => defined la /\ defined lb /\ (forall a b, la a -> lb b -> c = f a b)) _.
Next Obligation.
  destruct H2, H6.
  rewrite (H7 x x0), (H5 x x0); auto.
  reflexivity.
Qed.

(* note: thes only work on eq for now *)


Program Definition bind_lone {A B}
        (t : lone A _) (f : A -> lone B _) : lone B _ :=
  mk_lone (fun b => exists a : A, t a /\ f a b) _.
Next Obligation.
  apply (lone_unique (f H0)); auto.
  pose proof lone_unique t H H0 H3 H1.
  subst.
  auto.
Qed.

Program Definition lift_one {A B}
        (f : A -> B) : one A _ -> one B _ :=
  fun oa =>
    mk_one (fun b => forall a, oa a -> b = f a) _ _.
Next Obligation.
  destruct oa as [? [a ?]].
  simpl in *.
  rewrite (H a), (H0 a); auto.
Qed.
Next Obligation.
  destruct oa as [[fa lone_a] [a one_a]].
  simpl in *.
  exists (f a).
  intros.
  rewrite (lone_a a a0); auto.
Qed.

Program Definition lift_one2 {A B C} (f : A -> B -> C) : one A _ -> one B _ -> one C _ :=
  fun oa ob =>
    mk_one (fun c => forall a b, oa a -> ob b -> c = f a b) _ _.
Next Obligation.
  destruct oa as [? [a ?]].
  destruct ob as [? [b ?]].
  simpl in *.
  rewrite (H a b), (H0 a b); auto.
Qed.
Next Obligation.
  destruct oa as [[fa lone_a] [a one_a]].
  destruct ob as [[fb lone_b] [b one_b]].
  simpl in *.
  exists (f a b).
  intros.
  rewrite (lone_a a a0); auto.
  rewrite (lone_b b b0); auto.
Qed.
