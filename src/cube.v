Require Import Coq.fourier.Fourier.
Require Import Coq.Reals.Reals.

Local Open Scope R.

Definition Rcube r := r ^ 3.

Definition Rcube_root x : R :=
  match total_order_T 0 x with
  | inleft (left _) => Rpower x (1/3)
  | inleft (right _) => 0
  | inright _ => - Rpower (-x) (1/3)
  end.

(* Lemma Rcube_monotone a b : (a <= b -> Rcube a <= Rcube b). *)
(* Proof. *)
(*   unfold Rcube. *)
(*   intros. *)
(*   destruct (Rle_lt_dec 0 a), (Rle_lt_dec 0 b); try fourier. { *)
(*     apply pow_incr; auto. *)
(*   } { *)
(*     apply (Rle_trans _ 0). { *)
(*       unfold pow. *)
(*       left. *)
(*       replace (a * _) with (- (- a * (a * a))) by ring. *)
(*       apply Ropp_lt_gt_0_contravar. *)
(*       apply Rmult_lt_0_compat; try fourier. *)
(*       replace (a * a) with (- a * - a) by ring. *)
(*       apply Rmult_lt_0_compat; try fourier. *)
(*     } { *)
(*       repeat apply Rmult_le_pos; auto. *)
(*       fourier. *)
(*     } *)
(*   } { *)
(*     apply Ropp_le_cancel. *)
(*     replace (- a ^ 3) with ((- a)^3) by ring. *)
(*     replace (- b ^ 3) with ((- b)^3) by ring. *)
(*     apply pow_incr. *)
(*     split; fourier. *)
(*   } *)
(* Qed. *)

Lemma Rcube_root_of_cube r : Rcube_root (Rcube r) = r.
Proof.
  assert (case_pos : forall r, 0 < r ^ 3 -> Rpower (r ^ 3) (1 / 3) = r). {
    clear.
    intros.
    assert (0 < r). {
      destruct (Rlt_le_dec 0 r); try fourier.
      contradict H.
      apply RIneq.Rle_not_lt.
      replace r with (- - r) in * by ring.
      set (- r) in *.
      clearbody r1.
      apply Ropp_le_cancel.
      ring_simplify.
      assert (0 <= r1) by fourier.
      repeat (apply Rmult_le_pos; try fourier).
    }
    rewrite <- Rpower_pow in *; auto.
    rewrite Rpower_mult.
    replace (_ * _) with 1 by (cbn; field).
    apply Rpower_1.
    auto.
  }

  unfold Rcube_root, Rcube.
  destruct total_order_T as [[|] |]. {
    apply case_pos.
    auto.
  } {
    symmetry in e.
    destruct (Rmult_integral _ _ e); auto.
    destruct (Rmult_integral _ _ H); auto.
    ring_simplify in H0.
    auto.
  } {
    replace r with (- - r) in * by ring.
    set (- r) in *.
    clearbody r1.
    clear r.
    apply Ropp_lt_gt_contravar in r0.
    hnf in r0.
    ring_simplify in r0.
    f_equal.
    replace (- (- r1) ^ 3) with (r1 ^ 3) by ring.
    apply case_pos.
    auto.
  }
Qed.

Lemma Rcube_of_cube_root : forall r, Rcube (Rcube_root r) = r.
Proof.
  unfold Rcube_root, Rcube.
  assert (case_pos : forall r, 0 < r -> (Rpower r (1 / 3)) ^ 3 = r). {
    intros.
    rewrite <- Rpower_pow in *. {
      rewrite Rpower_mult.
      replace (_ * _) with 1 by (cbn; field).
      apply Rpower_1.
      auto.
    } {
      apply exp_pos.
    }
  }
  intros.
  destruct total_order_T as [[|] |]. {
    apply case_pos; auto.
  } {
    subst.
    ring.
  } {
    specialize (case_pos (-r)).
    set (Rpower _ _) in *.
    replace ((- r1) ^ 3) with (- r1 ^ 3) by ring.
    rewrite case_pos; solve [ring | fourier].
  }
Qed.
