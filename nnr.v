(* Tested with coq 8.5pl1 *)

Require Import Basics.
Require Import Reals.
Require Import Coq.fourier.Fourier.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Morphisms.
Require Import ProofIrrelevance.

Delimit Scope ennr_scope with ennr.

Local Open Scope R.
Local Open Scope ennr_scope.
Export RingSyntax.

Inductive ennr :=
| finite (r : R) (r_pos : 0 <= r)
| infinite
.
Notation "R+" := ennr : type_scope.

(* equivalence modulo proofs of positivity *)
(* Definition ennr_eq (a b : R+) : Prop := *)
(*   match a, b with *)
(*   | finite ra _, finite rb _ => ra = rb *)
(*   | _, _ => a = b *)
(*   end. *)
(* Infix "==" := ennr_eq. *)

Program Definition ennr_0 := finite 0 (Rle_refl _).
Program Definition ennr_1 := finite 1 Rle_0_1.
Notation "0" := ennr_0.
Notation "1" := ennr_1.

Definition ennr_plus (a b : R+) : R+ :=
  match a, b with
  | finite ra ra_pos, finite rb rb_pos
    => finite (ra + rb) (Rplus_le_le_0_compat _ _ ra_pos rb_pos)
  | _, _ => infinite
  end.
Infix "+" := ennr_plus.

Definition ennr_mult (a b : R+) : R+ :=
  match a, b with
  | finite ra ra_pos, finite rb rb_pos
    => finite (ra * rb) (Rmult_le_pos _ _ ra_pos rb_pos)
  | finite ra ra_pos, infinite
    => if Req_EM_T 0 ra then 0 else infinite
  | infinite, finite rb rb_pos
    => if Req_EM_T 0 rb then 0 else infinite
  | infinite, infinite
    => infinite
  end.
Infix "*" := ennr_mult.

Lemma finite_inj r0 r0_pos r1 r1_pos :
  r0 = r1 ->
  finite r0 r0_pos = finite r1 r1_pos.
Proof.
  intros.
  subst.
  f_equal.
  apply proof_irrelevance.
Qed.
Hint Immediate finite_inj.

Ltac ennr := apply finite_inj; try (simpl; ring).

Lemma ennr_add_0_l : forall n, 0 + n = n.
Proof.
  destruct n; auto; ennr.
Qed.

Lemma ennr_add_comm : forall n m, n + m = m + n.
Proof.
  destruct n, m; auto; ennr.
Qed.

Lemma ennr_add_assoc : forall n m p, n + (m + p) = (n + m) + p.
Proof.
  destruct n, m, p; auto; ennr.
Qed.

Lemma ennr_mul_1_l : forall n, 1 * n = n.
Proof.
  destruct n; simpl; auto.
  - ennr.
  - destruct Req_EM_T; simpl; auto.
    fourier.
Qed.

Lemma ennr_mul_0_l : forall n, 0 * n = 0.
Proof.
  destruct n; simpl; auto.
  - ennr.
  - destruct Req_EM_T; simpl; auto.
    contradict n.
    auto.
Qed.

Lemma ennr_mul_comm : forall n m, n * m = m * n.
Proof.
  destruct n, m; auto; ennr.
Qed.

Lemma ennr_mul_assoc : forall n m p, n * (m * p) = (n * m) * p.
Proof.
  assert (forall r0 r1, 0 = r0 * r1 -> 0 <> r0 -> 0 <> r1 -> False)%R. {
    intros.
    contradict H0.
    replace r0 with ((r0 * r1) * / r1)%R. {
      rewrite <- H.
      ring.
    } {
      rewrite Rmult_assoc.
      rewrite Rinv_r; auto.
      ring.
    }
  }

  destruct n, m, p;
    repeat (try destruct Req_EM_T; simpl);
    subst;
    auto;
    solve
      [ ennr
      | contradict n; ring
      | contradict n0; ring
      | contradict H; eauto
      ].
Qed.

Lemma ennr_distr_l : forall n m p, (n + m) * p = n * p + m * p.
Proof.
  destruct n, m, p;
    repeat (try destruct Req_EM_T; simpl);
    subst;
    auto;
    try ennr.
  {
    contradict n.
    rewrite e.
    ring.
  } {
    contradict n.
    apply Rle_antisym; auto.
    rewrite e.
    replace r with (r + 0)%R at 1 by ring.
    apply Rplus_le_compat; auto.
    apply Rle_refl.
  }
  contradict n; ring.
Qed.

Arguments ennr_plus _ _ : simpl never.
Arguments ennr_mult _ _ : simpl never.

Definition ennr_semiring :=
  mk_srt ennr_0 ennr_1 ennr_plus ennr_mult eq
    ennr_add_0_l
    ennr_add_comm
    ennr_add_assoc
    ennr_mul_1_l
    ennr_mul_0_l
    ennr_mul_comm
    ennr_mul_assoc
    ennr_distr_l
.

Definition ennr_lt (a b : R+) : Prop :=
  match a, b with
  | finite ra _, finite rb _ => ra < rb
  | finite _ _, infinite => True
  | infinite, _ => False
  end.
Definition ennr_gt a b := ennr_lt b a.
Definition ennr_le a b := ennr_lt a b \/ a = b.
Definition ennr_ge a b := ennr_gt a b \/ a = b.
Infix "<" := ennr_lt.
Infix "<=" := ennr_le.
Infix ">" := ennr_gt.
Infix ">=" := ennr_ge.

Lemma ennr_gt_dec (a b : R+) : {a > b} + {~ a > b}.
Proof.
  destruct a, b; simpl; auto.
  apply Rgt_dec.
Qed.

Notation "a  '[>]'  b" := (ennr_gt_dec a b) (at level 70, no associativity).

Add Ring ennr_semiring : ennr_semiring.