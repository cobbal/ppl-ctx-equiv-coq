Require Import Basics.
Require Import Reals.
Require Import List.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import nnr.
Require Import syntax.
Require Import utils.
Require Import Coq.Classes.Morphisms.
Require Import relations.
Require Import ctxequiv.

Require Import micromega.Lia.
(* Local Open Scope R. *)

Transparent π.
Arguments π _ _ _ : simpl never.

Notation "x ~> y" := (Arrow x y) (at level 69, right associativity, y at level 70).
Notation "` x" := (e_var x) (at level 72).
Notation "'λ' τ , e" := (e_lam τ e) (at level 69, right associativity).
Notation "e0 @ e1" := (e_app e0 e1) (at level 68, left associativity).
Notation "e0 +! e1" := (e_plus e0 e1) (at level 68, left associativity).

Lemma left_tc {e} :
  (TC · ⊢ e : ℝ) ->
  (TC · ⊢ e_real 0 +! e : ℝ).
Proof.
  repeat constructor; auto.
Qed.

Lemma ext_len {X n} {Γ : Env X} τ :
  n <= length Γ ->
  S n <= length (extend Γ τ).
Proof.
  simpl; lia.
Qed.

Lemma simplish {e}
      (He : (TC · ⊢ e : ℝ))
      σ A :
  eval_in (left_tc He) A σ = eval_in He A (π 1 σ).
Proof.
  unfold eval_in.
  unfold ev, ew.
  decide_eval _ as [v0 w0 ex0 u0]. {
    inversion ex0; subst; try absurd_Val.
    inversion X; subst.
    inversion H0; subst.
    simpl in *.
    decide_eval _ as [v3 w3 ex3 u3].
    simpl.
    pose proof big_preservation He ex3.
    destruct v3 using Val_rect; try solve [inversion X1].
    simpl in *.
    pose proof EPlus σ X ex3.
    rewrite nnr_mult_one_l in *.
    repeat rewrite Rplus_0_l in *.
    specialize (u0 (v_real r : Val, _) X2).
    inversion u0; subst.
    repeat f_equal; try nnr.
    apply WT_Val_eq.
    simpl.
    f_equal.
    ring.
  } {
    decide_eval _ as [v0 w0 ex0 u0]. {
      contradict not_ex.
      pose proof big_preservation He ex0.
      destruct v0 using Val_rect; try solve [inversion X].

      exists (v_real (0 + r) : Val, nnr_1 [*] w0).
      pose proof EPure' (π 0 σ) (v_real 0) _ eq_refl.
      apply (EPlus σ X0 ex0).
    }
  }
Qed.

Lemma πL_same_integral f :
  Integration (f ∘ πL) μEntropy = Integration f μEntropy.
Proof.
  replace (f ∘ πL) with (fun σ => block (fun σL σR => f σL) (πL σ) (πR σ)) by auto.
  rewrite lemma_9.
  unfold block.
  simpl.
  f_equal.
  extensionality σ.
  erewrite int_const_entropy; eauto.
Qed.

Lemma πR_same_integral f :
  Integration (f ∘ πR) μEntropy = Integration f μEntropy.
Proof.
  replace (f ∘ πR) with (fun σ => block (fun σL σR => f σR) (πL σ) (πR σ)) by auto.
  rewrite lemma_9.
  unfold block.
  simpl.
  erewrite int_const_entropy; eauto.
Qed.

Lemma project_same_integral f n :
  Integration (f ∘ π n) μEntropy = Integration f μEntropy.
Proof.
  induction n. {
    unfold π.
    apply πL_same_integral.
  } {
    rewrite <- IHn.
    clear IHn.
    replace (f ∘ π (S n)) with (f ∘ π n ∘ πR) by auto.
    apply πR_same_integral.
  }
Qed.

Lemma add_zero_related {e}
      (He : (TC · ⊢ e : ℝ)) :
  (EXP · ⊢ e_real 0 +! e ≈ e : ℝ).
Proof.
  refine (mk_related_exprs (left_tc He) He _).
  simpl.
  intros ρ0 ρ1 Hρ.
  rewrite (wt_nil_unique ρ0) in *.
  rewrite (wt_nil_unique ρ1) in *.
  clear ρ0 ρ1 Hρ.

  unfold subst_of_WT_Env; simpl.
  rewrite subst_id.
  exists (left_tc He).
  exists He.
  intros A0 A1 HA.

  unfold μ.
  setoid_rewrite simplish.

  replace (fun σ : Entropy => _) with
  (eval_in He A0 ∘ π 1) by auto.
  rewrite project_same_integral.
  f_equal.
  extensionality σ.
  f_equal.
  extensionality x.
  apply HA.
  destruct x using WT_Val_rect; try discriminate.
  reflexivity.
Qed.

Print Assumptions add_zero_related.

Lemma swap_same_integral f :
  Integration (fun σ => f (πL σ) (πR σ)) μEntropy =
  Integration (fun σ => f (πR σ) (πL σ)) μEntropy.
Proof.
  rewrite lemma_9.
  replace (fun σ => f (πR σ) (πL σ)) with (fun σ => flip f (πL σ) (πR σ)) by auto.
  rewrite lemma_9.
  apply tonelli_3; repeat constructor.
Qed.

Lemma swap_same_integral' f :
  Integration f μEntropy =
  Integration (fun σ => f (join (πR σ) (πL σ))) μEntropy.
Proof.
  enough (f = (fun σ => block (fun σL σR => f (join σL σR)) (πL σ) (πR σ))). {
    rewrite H at 1.
    apply swap_same_integral.
  } {
    extensionality σ.
    unfold block.
    f_equal.
    rewrite join_πL_πR.
    auto.
  }
Qed.

Require Import FinFun.

Definition shuf (s : nat -> nat) : Entropy -> Entropy
  := fun σ => σ ∘ s.

(* don't put shuf in the axiom for now *)
Lemma int_inj_entropy_ax f {i : nat -> nat} :
  Injective i ->
  Integration f μEntropy =
  Integration (fun σ => f (σ ∘ i)) μEntropy.
Admitted.

Lemma int_inj_entropy f {i : nat -> nat} :
  Injective i ->
  Integration f μEntropy =
  Integration (f ∘ shuf i) μEntropy.
Proof.
  apply int_inj_entropy_ax.
Qed.

Lemma πL_n_inj : Injective πL_n.
Proof.
  intros ? ? ?.
  unfold πL_n in *.
  lia.
Qed.

Lemma πR_n_inj : Injective πR_n.
  intros ? ? ?.
  unfold πR_n in *.
  lia.
Qed.

Lemma int_πL_entropy f :
  Integration f μEntropy =
  Integration (f ∘ πL) μEntropy.
Proof.
  replace πL with (shuf πL_n) by auto.
  apply int_inj_entropy.
  apply πL_n_inj.
Qed.

Lemma inj_comp {A B C} {f : B -> C} {g : A -> B} :
  Injective f -> Injective g -> Injective (f ∘ g).
Proof.
  intros ? ? ? ? ?.
  unfold compose in *.
  apply H0.
  apply H.
  auto.
Qed.

Lemma π_n_inj i : Injective (π_n i).
Proof.
  induction i; simpl. {
    apply πL_n_inj.
  } {
    apply inj_comp; auto.
    apply πR_n_inj.
  }
Qed.

Definition swap := fun σ => join (πR σ) (πL σ).
Definition swap_n := join' πR_n πL_n.
Lemma swap_equiv (σ : Entropy) :
  σ ∘ swap_n = swap σ.
Proof.
  intros.
  unfold swap, swap_n, πL, πR, join, compose, join'.
  extensionality x.
  destruct Nat.even; auto.
Qed.
Lemma swap_n_inj : Injective swap_n.
Proof.
  intros ? ? ?.
  unfold swap_n, join', πR_n, πL_n in H.
  remember (Nat.even x).
  remember (Nat.even y).
  destruct b, b0; try lia. {
    assert (Even.even x) by (apply Even.even_equiv, Nat.even_spec; auto).
    assert (Even.even y) by (apply Even.even_equiv, Nat.even_spec; auto).
    fold (Nat.double (Nat.div2 x)) in H.
    fold (Nat.double (Nat.div2 y)) in H.
    do 2 rewrite <- Div2.even_double in H; auto.
  } {
    assert (forall z, false = Nat.even z -> Even.odd z). {
      intros.
      apply Even.odd_equiv, Nat.odd_spec.
      rewrite <- Nat.negb_even.
      apply Bool.negb_true_iff.
      auto.
    }
    apply H0 in Heqb.
    apply H0 in Heqb0.
    clear H0.
    assert (S (Nat.double (Nat.div2 x)) = S (Nat.double (Nat.div2 y)))
      by (f_equal; apply H).
    do 2 rewrite <- Div2.odd_double in H0; auto.
  }
Qed.

Definition swap_01 σ := join (π 1 σ) (join (π 0 σ) (πR (πR σ))).
Definition swap_01_n := join' (π_n 1) (join' (π_n 0) (πR_n ∘ πR_n)).

Lemma swap_01_equiv :
  shuf swap_01_n = swap_01.
Proof.
  extensionality σ.
  unfold shuf, swap_01, swap_01_n, compose, join.
  repeat rewrite <- π_π_n_correspond.
  extensionality n.
  unfold compose, join'.
  destruct Nat.even; auto.
  destruct Nat.even; auto.
Qed.

Lemma swap_01_0 σ : (π 0 (swap_01 σ) = π 1 σ).
Proof.
  apply πL_join.
Qed.
Lemma swap_01_1 σ : (π 1 (swap_01 σ) = π 0 σ).
Proof.
  unfold swap_01.
  unfold π.
  rewrite πR_join.
  rewrite πL_join.
  auto.
Qed.

Lemma make_odd z : false = Nat.even z -> Even.odd z.
Proof.
  intros.
  apply Even.odd_equiv, Nat.odd_spec.
  rewrite <- Nat.negb_even.
  apply Bool.negb_true_iff.
  auto.
Qed.

Lemma make_even z : true = Nat.even z -> Even.even z.
Proof.
  intros.
  apply Even.even_equiv, Nat.even_spec.
  auto.
Qed.

Ltac make_even_and_odd :=
  repeat
    match goal with
    | [ H : true = Nat.even _ |- _ ] => apply make_even in H
    | [ H : false = Nat.even _ |- _ ] => apply make_odd in H
    end.

Ltac fold_doubles :=
  repeat match goal with
  | [ |- context[ (?n + ?n)%nat ] ] => progress fold (Nat.double n)
  | [ H : context[ (?n + ?n)%nat ] |- _] => progress fold (Nat.double n) in H
  end.

Lemma even_div_2_inj (x y : nat) :
  Nat.even x = Nat.even y ->
  Nat.div2 x = Nat.div2 y ->
  x = y.
Proof.
  intros.
  repeat remember (Nat.even _) in H.
  destruct b, b0; try discriminate H; make_even_and_odd. {
    rewrite (Div2.even_double x); auto.
    rewrite (Div2.even_double y); auto.
  } {
    rewrite (Div2.odd_double x); auto.
    rewrite (Div2.odd_double y); auto.
  }
Qed.

Lemma double_inj : Injective Nat.double.
Proof.
  intros ? ? ?.
  unfold Nat.double in H.
  lia.
Qed.

Lemma S_inj : Injective S.
Proof.
  intros ? ? ?.
  injection H.
  auto.
Qed.

Lemma swap_01_n_inj : Injective swap_01_n.
Proof.
  intros ? ? ?.
  unfold swap_01_n, join' in H.
  simpl in H.

  unfold compose, πL_n, πR_n in H.
  (* repeat remember (Nat.even _) in H. *)

  repeat remember (Nat.even _) in H.
  apply even_div_2_inj;
destruct b, b0, b1, b2;
try pose proof (eq_trans (eq_sym Heqb) Heqb1);
try pose proof (eq_trans (eq_sym Heqb0) Heqb2);
auto; try lia. {
    make_even_and_odd.
    fold_doubles.
    repeat (rewrite <- Div2.even_double in H; auto).
  } {
    make_even_and_odd.
    fold_doubles.
    repeat (apply double_inj in H || apply S_inj in H).
    apply even_div_2_inj; auto.
  }
Qed.

Lemma add_comm_related e1 e2 :
  (TC · ⊢ e1 : ℝ) ->
  (TC · ⊢ e2 : ℝ) ->
  (EXP · ⊢ e1 +! e2 ≈ e2 +! e1 : ℝ).
Proof.
  intros He1 He2.

  refine (mk_related_exprs (TCPlus He1 He2) (TCPlus He2 He1) _).
  intros ρ0 ρ1 Hρ.
  rewrite (wt_nil_unique ρ0) in *.
  rewrite (wt_nil_unique ρ1) in *.
  clear ρ0 ρ1 Hρ.

  unfold subst_of_WT_Env; simpl.
  rewrite 2 subst_id.
  exists (TCPlus He1 He2).
  exists (TCPlus He2 He1).
  intros A0 A1 HA.

  unfold μ.

  rewrite (int_inj_entropy _ swap_01_n_inj).
  rewrite swap_01_equiv.

  f_equal.
  extensionality σ.
  unfold compose.

  unfold eval_in, ev, ew.
  decide_eval _ as [v0 w0 ex0 u0]. {
    inversion ex0; subst; try absurd_Val.

    rewrite swap_01_0 in X.
    rewrite swap_01_1 in X0.
    pose proof EPlus σ X0 X as erev.

    decide_eval _ as [v3 w3 ex3 u3].
    inversion ex3; try absurd_Val.
    subst.
    simpl.
    specialize (u3 (_, _) erev).
    inversion u3.
    f_equal. {
      unfold Indicator.
      f_equal.
      apply HA.
      simpl.
      rewrite H0.
      unfold V_rel_real.
      simpl.
      apply Val_eq.
      simpl.
      f_equal.
      ring.
    } {
      nnr.
      simpl.
      rewrite H1.
      ring.
    }
  } {
    decide_eval _ as [v3 w3 ex3 u3].
    contradict not_ex.
    inversion ex3; subst; try absurd_Val.
    rewrite <- swap_01_0 in X0.
    rewrite <- swap_01_1 in X.
    eexists (v_real _ : Val , _).
    econstructor; eauto.
  }
Qed.

Print Assumptions add_comm_related.

Definition ex_left e1 e2 := (λ ℝ, e1.[ren S] +! `O) @ e2.
Definition ex_right e1 e2 := e1 +! e2.

Lemma tc_left {Γ e1 e2}
      (He1 : TC Γ ⊢ e1 : ℝ)
      (He2 : TC Γ ⊢ e2 : ℝ) :
  (TC Γ ⊢ ex_left e1 e2 : ℝ).
Proof.
  assert (TC (extend Γ ℝ) ⊢ e1.[ren S] : ℝ). {
    apply (ty_ren He1).
    auto.
  }
  repeat econstructor; eauto.
Qed.

Lemma tc_right {Γ e1 e2}
      (He1 : TC Γ ⊢ e1 : ℝ)
      (He2 : TC Γ ⊢ e2 : ℝ) :
  (TC Γ ⊢ ex_right e1 e2 : ℝ).
Proof.
  repeat constructor; auto.
Qed.

Lemma break_right {Γ e1 e2}
      (ρ : WT_Env Γ)
      (σ0 σ1 σr : Entropy)
      (He1 : (TC Γ ⊢ e1 : ℝ))
      (He2 : (TC Γ ⊢ e2 : ℝ))
      A :
  eval_in (close ρ (tc_right He1 He2)) A (join σ0 (join σ1 σr)) =
  option0 (plus_in A <$> ev (close ρ He1) σ0 <*> ev (close ρ He2) σ1)
          [*] ew (close ρ He1) σ0
          [*] ew (close ρ He2) σ1.
Proof.
  intros.
  unfold eval_in.
  unfold ev at 1, ew at 1.
  decide_eval _ as [v0 w0 ex0 u0]. {
    inversion ex0; subst; try absurd_Val.
    unfold π in *.
    repeat rewrite πR_join in *.
    rewrite πL_join in *.
    unfold ev, ew.
    simpl.

    decide_eval (close ρ He1) as [v3 w3 ex3 u3].
    pose proof big_preservation (close ρ He1) ex3.
    destruct v3 using Val_rect; inversion X1; subst.

    decide_eval (close ρ He2) as [v5 w5 ex5 u5].
    pose proof big_preservation (close ρ He2) ex5.
    destruct v5 using Val_rect; inversion X2; subst.

    rewrite <- nnr_mult_assoc.

    unfold plus_in.
    simpl in *.

    destruct is_v0, is_v1.

    specialize (u3 (_, _) X).
    specialize (u5 (_, _) X0).
    inversion u3.
    inversion u5.
    subst.

    repeat f_equal.
    apply WT_Val_eq.
    auto.
  } {
    simpl.
    unfold ev, ew.
    decide_eval _ as [v3 w3 ex3 u3].
    decide_eval _ as [v4 w4 ex4 u4].
    contradict not_ex.

    pose proof big_preservation (close ρ He1) ex3.
    destruct v3 using Val_rect; inversion X; subst.

    pose proof big_preservation (close ρ He2) ex4.
    destruct v4 using Val_rect; inversion X0; subst.

    eexists (v_real (r + r0) : Val, w3 [*] w4).

    econstructor; eauto. {
      simpl.
      rewrite πL_join.
      eauto.
    } {
      unfold π.
      rewrite πR_join.
      rewrite πL_join.
      eauto.
    }
  }
Qed.

Lemma break_left {Γ e1 e2}
      (ρ : WT_Env Γ)
      (He1 : (TC Γ ⊢ e1 : ℝ))
      (He2 : (TC Γ ⊢ e2 : ℝ))
      σ A :
  let σe1 := (π 0 (π 2 σ)) in
  let σe2 := (π 1 σ) in
  eval_in (close ρ (tc_left He1 He2)) A σ =
  option0 (plus_in A <$> ev (close ρ He1) σe1 <*> ev (close ρ He2) σe2)
          [*] ew (close ρ He1) σe1
          [*] ew (close ρ He2) σe2.
Proof.
  intros.

  unfold eval_in.
  unfold ev at 1, ew at 1.
  decide_eval _ as [v0 w0 ex0 u0]. {
    pose proof big_preservation (close ρ (tc_left He1 He2)) ex0.
    destruct v0 using Val_rect; inversion X; subst.
    inversion ex0; subst; try absurd_Val.
    inversion X0; subst.
    inversion H0; subst.
    dependent destruction X2.
    simpl in *.
    destruct is_v0, is_v1.

    replace (e1.[ren S].[up (subst_of_WT_Env ρ)].[v1 : Expr/])
    with e1.[subst_of_WT_Env ρ] in *
      by autosubst.

    unfold ev, ew.

    decide_eval (close ρ He1) as [v4 w4 ex4 u4].
    pose proof big_preservation (close ρ He1) ex4.
    destruct v4 using Val_rect; inversion X2; subst.

    decide_eval (close ρ He2) as [v5 w5 ex5 u5].
    pose proof big_preservation (close ρ He2) ex5.
    destruct v5 using Val_rect; inversion X3; subst.

    simpl.
    unfold plus_in, Indicator.
    simpl.
    replace (mk_WT_Val _ _) with (v_real (r0 + r1))
      by (apply WT_Val_eq; auto).

    specialize (u4 (_, _) X2_1).
    specialize (u5 (_, _) X1).
    inversion u4.
    inversion u5.
    subst.

    inversion X2_2; subst.
    inversion H1; subst.
    nnr.
  } {
    simpl.
    unfold ev, ew.
    decide_eval (close ρ He1) as [v4 w4 ex4 u4].
    pose proof big_preservation (close ρ He1) ex4.
    destruct v4 using Val_rect; inversion X; subst.

    decide_eval (close ρ He2) as [v5 w5 ex5 u5].
    pose proof big_preservation (close ρ He2) ex5.
    destruct v5 using Val_rect; inversion X0; subst.

    contradict not_ex.
    eexists (v_real (r + r0) : Val, _).
    eapply EApp; eauto. {
      eapply EPure'.
      reflexivity.
    } {
      simpl.
      replace (e1.[ren S].[up (subst_of_WT_Env ρ)].[e_real r0 : Expr/])
      with e1.[subst_of_WT_Env ρ] in *
        by autosubst.
      apply EPlus with (is_v0 := I) (is_v1 := I); eauto.
      apply EPure'.
      reflexivity.
    }
  }
Qed.

(* map (π 0 (π 2 σ)) over to (π 0 σ) *)
Definition kajigger σ := join (π 0 (π 2 σ)) (join (π 1 σ) (π 0 σ)).
Definition kajigger_n := (join' (π_n 2 ∘ π_n 0) (join' (π_n 1) (π_n 0))).

Lemma kajigger_02 σ : (π 0 (kajigger σ)) = π 0 (π 2 σ).
Proof.
  apply πL_join.
Qed.
Lemma kajigger_1 σ : (π 1 (kajigger σ) = π 1 σ).
Proof.
  unfold kajigger.
  unfold π.
  rewrite πR_join.
  rewrite πL_join.
  auto.
Qed.

Lemma kajigger_equiv :
  shuf kajigger_n = kajigger.
Proof.
  extensionality σ.
  unfold shuf, kajigger, kajigger_n, compose, join.
  repeat rewrite <- π_π_n_correspond.
  extensionality n.
  unfold compose, join'.
  destruct Nat.even; auto.
  destruct Nat.even; auto.
Qed.

Lemma kajigger_n_inj : Injective kajigger_n.
Proof.
  intros ? ? ?.
  unfold kajigger_n, join' in H.
  simpl in H.

  unfold compose, πL_n, πR_n in H.

  repeat remember (Nat.even _) in H.
  apply even_div_2_inj;
destruct b, b0, b1, b2;
try pose proof (eq_trans (eq_sym Heqb) Heqb1);
try pose proof (eq_trans (eq_sym Heqb0) Heqb2);
auto; try lia. {
    make_even_and_odd.
    fold_doubles.
    rewrite <- Div2.even_double in H; auto.
    rewrite <- Div2.odd_double in H; auto.
    rewrite <- Div2.even_double in H; auto.
    rewrite <- Div2.odd_double in H; auto.
  } {
    make_even_and_odd.
    fold_doubles.
    repeat (apply double_inj in H || apply S_inj in H).
    apply even_div_2_inj; auto.
  }
Qed.

Lemma int_by_dirac {A} (f : A -> R+) (v : A) :
  Integration f (dirac v) = f v.
Proof.
  unfold dirac.
  rewrite riemann_def_of_lebesgue_integration.
  pose proof integration_of_indicator lebesgue_measure.
  unfold Indicator in *.
  rewrite H.
  clear H.
  apply lebesgue_measure_interval.
Qed.

Lemma beta_addition {Γ e1 e2} :
  (TC Γ ⊢ e1 : ℝ) ->
  (TC Γ ⊢ e2 : ℝ) ->
  (EXP Γ ⊢ ex_left e1 e2 ≈ ex_right e1 e2 : ℝ).
Proof.
  intros He1 He2.

  refine (mk_related_exprs (tc_left He1 He2) (tc_right He1 He2) _).
  intros.

  (* destruct ρ0 as [ρ0 Hρ0]. *)
  (* destruct ρ1 as [ρ1 Hρ1]. *)

  exists (close ρ0 (tc_left He1 He2)).
  exists (close ρ1 (tc_right He1 He2)).
  intros A0 A1 HA.

  unfold μ.

  symmetry.
  rewrite (int_inj_entropy _ kajigger_n_inj).
  symmetry.
  rewrite kajigger_equiv.

  setoid_rewrite break_left.

  assert (forall σ, σ = join (π 0 σ) (join (π 1 σ) (πR (πR σ)))). {
    intros.
    unfold π.
    rewrite 2 join_πL_πR.
    auto.
  }
  pose proof fun σ => break_right ρ1 (π 0 σ) (π 1 σ) (πR (πR σ)) He1 He2.
  setoid_rewrite <- H in H0.
  setoid_rewrite H0.
  clear H H0.

  unfold compose.
  setoid_rewrite kajigger_1.
  setoid_rewrite kajigger_02.

  setoid_rewrite <- (break_right ρ0 _ _ (π 0 σ)).
  setoid_rewrite <- (break_right ρ1 _ _ (π 0 x)).

  change (Integration (eval_in (close ρ0 (tc_right He1 He2)) A0 ∘ kajigger) μEntropy =
          Integration (eval_in (close ρ1 (tc_right He1 He2)) A1 ∘ kajigger) μEntropy).

  rewrite <- kajigger_equiv.
  rewrite <- 2 (int_inj_entropy _ kajigger_n_inj).

  apply related_close1; auto.
Qed.

Lemma the_whole_enchilada {Γ e1 e2} {He1 : TC Γ ⊢ e1 : ℝ} {He2 : TC Γ ⊢ e2 : ℝ} :
  ctx_equiv (tc_left He1 He2) (tc_right He1 He2).
Proof.
  pose proof related_is_contextually_equivalent (beta_addition He1 He2).
  destruct beta_addition.
  replace (tc_left _ _) with rel_expr_He0 by apply tc_unique.
  replace (tc_right _ _) with rel_expr_He1 by apply tc_unique.
  auto.
Qed.

Print Assumptions the_whole_enchilada.

Lemma pure_subst {Γ} (ρ : WT_Env Γ) x :
  is_pure (`x).[subst_of_WT_Env ρ].
Proof.
  unfold subst_of_WT_Env, downgrade_env.
  simpl.
  revert x.
  destruct ρ as [ρ Hρ].
  induction Hρ; intros; simpl; auto.
  destruct x; simpl; auto.
  destruct v as [a Ha].
  destruct a; try contradiction Ha; auto.
Qed.

Lemma beta_value {Γ e τ v τv} :
  is_pure v ->
  (TC Γ ⊢ (λ τv, e) @ v : τ) ->
  (EXP Γ ⊢ (λ τv, e) @ v ≈ e.[v/] : τ).
Proof.
  intros v_val Happ.
  inversion Happ; subst.
  inversion X; subst.
  rename X into Hlam, X0 into Hv, X1 into He.

  assert (Hsubst : TC Γ ⊢ e.[v/] : τ). {
    apply (ty_subst He).
    intros.
    destruct x; simpl in *. {
      inversion H; subst.
      auto.
    } {
      constructor; auto.
    }
  }

  split; auto.
  intros ρ0 ρ1 Hρ.
  eexists (close ρ0 Happ).
  eexists (close ρ1 Hsubst).

  intros A0 A1 HA.
  unfold μ.

  replace (close ρ0 Happ) with (TCApp (close ρ0 Hlam) (close ρ0 Hv)) by apply tc_unique.
  setoid_rewrite by_theorem_15_app.

  setoid_rewrite (pure_is_dirac (close ρ0 Hlam) I).
  rewrite int_by_dirac.

  assert (is_pure v.[subst_of_WT_Env ρ0]). {
    destruct v; try contradiction v_val; auto.
    apply pure_subst.
  }
  setoid_rewrite (pure_is_dirac (close ρ0 Hv) H).
  rewrite int_by_dirac.

  unfold compose.
  do_elim_apply_in.
  subst.

  enough (Integration (eval_in (close ρ0 Hsubst) A0) μEntropy =
          Integration (eval_in (close ρ1 Hsubst) A1) μEntropy). {

    replace (fun σ => eval_in (close ρ1 Hsubst) _ _) with (eval_in (close ρ1 Hsubst) A1)
      by (extensionality σ; auto).

    rewrite <- H0.

    f_equal.
    extensionality σ.

    assert (e.[v/].[subst_of_WT_Env ρ0] =
            e.[up (subst_of_WT_Env ρ0)].[WT_Val_of_pure (close ρ0 Hv) H : Expr/])
      by autosubst.

    unfold eval_in, ev, ew.
    decide_eval (ty_subst1 _ _) as [v0 w0 ex0 u0]. {
      decide_eval _ as [v1 w1 ex1 u1]. {
        rewrite <- H1 in *.
        specialize (u0 (_, _) ex1).
        inversion u0; subst.
        unfold Indicator.
        simpl.
        auto.
      } {
        contradict not_ex.
        rewrite <- H1 in *.
        eexists (_, _); eauto.
      }
    } {
      decide_eval _ as [v1 w1 ex1 u1].
      contradict not_ex.
      rewrite <- H1 in *.
      eexists (_, _); eauto.
    }
  }

  apply related_close1; auto.
Qed.

Print Assumptions beta_value.
