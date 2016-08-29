(* Tested with coq 8.5pl1 *)

Require Import Basics.
Require Import Reals.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

SearchPattern (nat -> R).
SearchAbout Rlt.
SearchAbout Rmin.

SearchAbout Rmult.

Local Open Scope R.

Record nnr := mknnr { _r : R; nnr_pos : 0 <= _r }.
Notation "R+" := nnr.

Program Definition nnr_mult (a b : R+) : R+ := mknnr (_r a * _r b) _.
Next Obligation.
  apply Rmult_le_pos.
  apply a.
  apply b.
Defined.
Hint Unfold nnr_mult.
Notation "a  '[*]'  b" := (nnr_mult a b) (at level 40, left associativity).

Program Definition nnr_plus (a b : R+) : R+ := mknnr (_r a + _r b) _.
Next Obligation.
  replace 0 with (0 + 0) by apply Rplus_0_l.
  apply Rplus_le_compat; [apply a | apply b].
Qed.
Hint Unfold nnr_plus.
Notation "a  '[+]'  b" := (nnr_plus a b) (at level 50, left associativity).

Program Definition nnr_0 := mknnr 0 (Rle_refl _).
Program Definition nnr_1 := mknnr 1 Rle_0_1.

Notation "a  '[>]'  b" := (Rgt_dec (_r a) b) (at level 70, no associativity).

Lemma nnr_eq_is_real_eq :
  forall (a b : R+), _r a = _r b -> a = b.
Proof.
  intros.
  destruct a as [a Ha], b as [b Hb].
  simpl in *.
  subst b.
  f_equal.
  apply proof_irrelevance.
Qed.
Ltac nnr := apply nnr_eq_is_real_eq.

Theorem nnr_mult_comm (a b : R+) : a [*] b = b [*] a.
Proof.
  nnr.
  apply Rmult_comm.
Qed.

Check Rmult_0_l.

Theorem nnr_mult_0_l (r : R+) : nnr_0 [*] r = nnr_0.
Proof.
  nnr.
  simpl.
  ring.
Qed.

Theorem nnr_mult_0_r (r : R+) : r [*] nnr_0 = nnr_0.
Proof.
  nnr.
  simpl.
  ring.
Qed.