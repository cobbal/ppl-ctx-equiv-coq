(* Tested with coq 8.5pl1 *)

Require Import Basics.
Require Import Reals.
Require Import Ensembles.
(* Require Import Coq.fourier.Fourier. *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

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

Program Definition nnr_div (a b : R+) (bpos : 0 < _r b) : R+ :=
 mknnr (_r a  / _r b) _.
Next Obligation.
  destruct a, b; simpl in *.

  apply Rmult_le_pos; auto.
  apply Rlt_le.
  apply Rinv_0_lt_compat; auto.
Qed.

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
Ltac nnr := apply nnr_eq_is_real_eq; try (simpl; ring).

Theorem nnr_mult_comm (a b : R+) : a [*] b = b [*] a.
Proof.
  nnr.
Qed.

Theorem nnr_mult_0_l (r : R+) : nnr_0 [*] r = nnr_0.
Proof.
  nnr.
Qed.

Theorem nnr_mult_0_r (r : R+) : r [*] nnr_0 = nnr_0.
Proof.
  nnr.
Qed.

Lemma nnr_mult_one_l (r : R+) : nnr_1 [*] r = r.
Proof.
  nnr.
Qed.

Lemma nnr_mult_one_r (r : R+) : r [*] nnr_1 = r.
Proof.
  nnr.
Qed.

Lemma nnr_mult_pos_l (a b : R+) :
  0 < _r (a [*] b) -> 0 < _r a.
Proof.
  intros.
  destruct a, b.
  simpl in *.

  destruct nnr_pos1. {
    apply (Rmult_lt_reg_r _r1); auto.
    rewrite Rmult_0_l; auto.
  } {
    contradict H.
    subst.
    rewrite Rmult_0_r.
    apply Rlt_irrefl.
  }
Qed.

Lemma nnr_mult_assoc (a b c : R+) :
  (a [*] b) [*] c = a [*] (b [*] c).
Proof.
  nnr.
Qed.
