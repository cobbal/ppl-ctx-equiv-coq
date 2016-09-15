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
Require Import micromega.Lia.
Import EqNotations.

(* Local Open Scope R. *)
Opaque π.

Inductive Ctx :=
| c_hole : Ctx
| c_app_l : Ctx -> Expr -> Ctx
| c_app_r : Expr -> Ctx -> Ctx
| c_factor : Ctx -> Ctx
| c_plus_l : Ctx -> Expr -> Ctx
| c_plus_r : Expr -> Ctx -> Ctx
| c_lam : Ty -> Ctx -> Ctx
.

Inductive tc_ctx (Γ : Env Ty) (τh : Ty) : Ctx -> Env Ty -> Ty -> Type :=
| TCXHole : tc_ctx Γ τh c_hole Γ τh
| TCXApp_l τa τr c ea :
    tc_ctx Γ τh c Γ (τa ~> τr) ->
    (TC Γ ⊢ ea : τa) ->
    tc_ctx Γ τh (c_app_l c ea) Γ τr
| TCXApp_r τa τr ef c :
    (TC Γ ⊢ ef : τa ~> τr) ->
    tc_ctx Γ τh c Γ τa  ->
    tc_ctx Γ τh (c_app_r ef c) Γ τr
| TCXFactor c :
    tc_ctx Γ τh c Γ ℝ ->
    tc_ctx Γ τh (c_factor c) Γ ℝ
| TCXPlus_l c er :
    tc_ctx Γ τh c Γ ℝ ->
    (TC Γ ⊢ er : ℝ) ->
    tc_ctx Γ τh (c_plus_l c er) Γ ℝ
| TCXPlus_r el c :
    (TC Γ ⊢ el : ℝ) ->
    tc_ctx Γ τh c Γ ℝ ->
    tc_ctx Γ τh (c_plus_r el c) Γ ℝ
| TCXPlus_lam τa τr c :
    (tc_ctx (extend Γ τa) τh c Γ τr) ->
    tc_ctx Γ τh (c_lam τa c) Γ (τa ~> τr)
.

Fixpoint plug (C : Ctx) (e : Expr) : Expr :=
  match C with
  | c_hole => e
  | c_app_l c0 e1 => e_app (plug c0 e) e1
  | c_app_r e0 c1 => e_app e0 (plug c1 e)
  | c_factor c0 => e_factor (plug c0 e)
  | c_plus_l c0 e1 => e_plus (plug c0 e) e1
  | c_plus_r e0 c1 => e_plus e0 (plug c1 e)
  | c_lam τa cbody => e_lam τa (plug cbody e)
  end.

Lemma tc_ctx_of_tc {ΓC Γe τe τr C e} :
  (TC Γe ⊢ e : τe) ->
  (tc_ctx ΓC τe C Γe τr) ->
  (TC ΓC ⊢ plug C e : τr).
Proof.
  intros.
  induction X0; simpl; try econstructor; eauto.
Defined.

Definition ctx_equiv {Γ τ} (e0 e1 : Expr)
           (He0 : (TC Γ ⊢ e0 : τ))
           (He1 : (TC Γ ⊢ e1 : τ)) :=
  forall C (HC : tc_ctx · τ C Γ ℝ) A,
    μ (tc_ctx_of_tc He0 HC) A = μ (tc_ctx_of_tc He1 HC) A.

Lemma all_envs_inhabited Γ : inhabited (WT_Env Γ).
Proof.
  constructor.
  induction Γ. {
    exact WT_nil.
  } {
    apply extend_WT_Env; auto.
    induction a. {
      exact (v_real 0).
    } {
      exists (mk_Val (e_lam a1 IHa2) I).
      constructor.
      replace (extend · a1) with (· ++ (extend · a1)) by auto.
      apply weakening.
      apply IHa2.
    }
  }
Qed.

Require Import micromega.Lia.

Lemma lookup_less {A} {Γ : Env A} {x τ} :
  (lookup Γ x = Some τ) ->
  x < length Γ.
Proof.
  intros.
  revert Γ H.
  induction x; intros. {
    destruct Γ; try discriminate.
    simpl.
    lia.
  } {
    destruct Γ; try discriminate.
    simpl in *.
    specialize (IHx Γ H).
    lia.
  }
Qed.

Lemma upn_foo n (x : Var) (σ : nat -> Expr) :
  x < n ->
  upn n σ x = ids x.
Proof.
  intros.
  revert n H.
  induction x, n; try lia; auto.

  unfold upn, up.
  fold up upn.
  simpl.

  intros.
  rewrite IHx; try lia.
  autosubst.
Qed.

Lemma subst_of_closed {Γ e τ} :
  (TC Γ ⊢ e : τ) ->
  forall σ,
    e.[upn (length Γ) σ] = e.
Proof.
  intros He σ.
  induction He; simpl; try solve [f_equal; auto].
  simpl.
  rewrite upn_foo; auto.
  exact (lookup_less e).
Qed.

Program Fixpoint close {Γ e τ} (ρ : WT_Env Γ) (He : (TC Γ ⊢ e : τ)) :
  (TC · ⊢ e.[subst_of_WT_Env ρ] : τ) :=
  match He with
  | TCReal r => TCReal r
  | @TCVar _ x _ Γx => _
  | TCLam Hbody => TCLam (body_subst _ _)
  | TCApp Hef Hea => TCApp (close ρ Hef) (close ρ Hea)
  | TCFactor He' => TCFactor (close ρ He')
  | TCSample => TCSample
  | TCPlus Hel Her => TCPlus (close ρ Hel) (close ρ Her)
  end.
Next Obligation.
  subst.
  unfold subst_of_WT_Env, downgrade_env.
  simpl.
  destruct ρ as [ρ Hρ].
  revert Γ ρ Hρ Γx.
  induction x; intros. {
    destruct Γ; try discriminate.
    inversion Γx; subst.
    simpl in *.
    inversion Hρ; subst.
    simpl.
    auto.
  } {
    simpl in *.
    destruct Γ; try discriminate.
    destruct Hρ; try discriminate.
    specialize (IHx _ _ Hρ Γx).
    auto.
  }
Qed.

Lemma related_close {Γ ρ0 ρ1}
      (Hρ : G_rel Γ ρ0 ρ1)
      {e0 e1 τ}
      (He : (EXP Γ ⊢ e0 ≈ e1 : τ)) :
  let (He0, He1, He) := He in
  forall A0 A1,
    A_rel τ A0 A1 ->
    μ (close ρ0 He0) A0 = μ (close ρ1 He1) A1.
Proof.
  destruct He as [He0 He1 He].
  intros A0 A1 HA.
  specialize (He _ _ Hρ).
  destruct He as [? [? He]].
  replace (close ρ0 He0) with x by apply tc_unique.
  replace (close ρ1 He1) with x0 by apply tc_unique.
  apply He.
  auto.
Qed.

Lemma related_close1 {Γ ρ0 ρ1 e τ}
      (Hρ : G_rel Γ ρ0 ρ1)
      (He : (TC Γ ⊢ e : τ)) :
  forall A0 A1,
    A_rel τ A0 A1 ->
    μ (close ρ0 He) A0 = μ (close ρ1 He) A1.
Proof.
  intros.
  pose proof related_close Hρ (fundamental_property He).
  destruct (fundamental_property He) as [x x0 _].
  replace x with He in * by apply tc_unique.
  replace x0 with He in * by apply tc_unique.
  apply H0.
  auto.
Qed.

Lemma μ_rewrite {e e'}
  : e = e' ->
    forall τ He He',
    @μ e τ He = @μ e' τ He'.
Proof.
  intros.
  subst.
  f_equal.
  apply tc_unique.
Qed.

Lemma close_nil {e τ} (He : TC · ⊢ e : τ)
  : μ (close WT_nil He) = μ He.
Proof.
  apply μ_rewrite.
  autosubst.
Qed.

Lemma related_is_contextually_equivalent {Γ τ e0 e1} :
  forall (re : (EXP Γ ⊢ e0 ≈ e1 : τ)),
    let (He0, He1, _) := re in
    ctx_equiv e0 e1 He0 He1.
Proof.
  intros.
  pose proof re as re'.
  destruct re as [He0 He1 _].
  intros ? ? ?.
  pose (A0 := narrow_event A).
  pose (A1 := narrow_event A).
  assert (A_rel ℝ A0 A1). {
    repeat intro.
    simpl in Hv.
    destruct v0 using Val_rect; try contradiction Hv.
    destruct v1 using Val_rect; try contradiction Hv.
    simpl in *.
    inversion Hv.
    auto.
  }
  replace A with (A0 : Event (WT_Val ℝ)) at 1 by apply narrow_cast_inverse.
  replace A with (A1 : Event (WT_Val ℝ)) at 1 by apply narrow_cast_inverse.
  clearbody A0 A1.
  clear A.

  (* revert HCe0 HCe1. *)
  revert HC.

  enough (forall ΓC ρC0 ρC1 (Hρ : G_rel ΓC ρC0 ρC1)
                 (HC : tc_ctx ΓC τ C Γ ℝ),
             μ (close ρC0 (tc_ctx_of_tc He0 HC)) A0 =
             μ (close ρC1 (tc_ctx_of_tc He1 HC)) A1). {

    intros.

    specialize (H0 _ _ _ G_rel_nil HC).
    (* do 2 set (close _ _) in H0. *)
    (* clearbody t t0. *)

    rewrite <- (close_nil (tc_ctx_of_tc He0 HC)).
    rewrite <- (close_nil (tc_ctx_of_tc He1 HC)).
    auto.
  }

  intros.
  revert ΓC ρC0 ρC1 Hρ HC A0 A1 H re'.
  generalize ℝ as τC.

  dependent induction HC; intros; simpl in *. {
    destruct re' as [_ _ re].
    specialize (re _ _ Hρ).
    destruct re as [? [? re]].
    specialize (re _ _ H).
    replace (close ρC0 He0) with x by apply tc_unique.
    replace (close ρC1 He1) with x0 by apply tc_unique.
    exact re.
  } {
    apply work_of_app; auto.
    apply related_close1; auto.
  } {
    apply work_of_app; auto.
    apply related_close1; auto.
  } {
    apply work_of_factor; auto.
  } {
    apply work_of_plus; auto.
    apply related_close1; auto.
  } {
    apply work_of_plus; auto.
    apply related_close1; auto.
  } {
    do 2 set (TCLam _).
    enough (dirac (WT_Val_of_pure t I) A0 =
            dirac (WT_Val_of_pure t0 I) A1). {
      subst t t0.
      rewrite <- 2 (pure_is_dirac (TCLam _) I) in H0.
      exact H0.
    }

    unfold dirac, Indicator; simpl.
    f_equal.
    apply H.

    split; auto.
    inversion t.
    inversion t0.
    subst.
    exists X; eauto.
    exists X0; eauto.
    clear t t0.
    rename X into Hplug0.
    rename X0 into Hplug1.

    intros va0 va1 Hva.
    exists (ty_subst1 va0 Hplug0).
    exists (ty_subst1 va1 Hplug1).
    intros Ar0 Ar1 HAr.

    specialize (IHHC He0 He1 _ _ (extend_grel _ _ Hρ Hva)).
    specialize (IHHC _ _ HAr re').

    (* ick *)
    set (plug c e0).[up (subst_of_WT_Env ρC0)].[va0 : Expr/].
    set (plug c e0).[subst_of_WT_Env (extend_WT_Env ρC0 va0)].
    assert (y = y0) by (subst y y0; autosubst).
    rewrite (μ_rewrite
               H0 τr
               (ty_subst1 va0 Hplug0)
               (close (extend_WT_Env ρC0 va0) (tc_ctx_of_tc He0 HC))).
    repeat subst.
    clear H0.

    set (plug c e1).[up (subst_of_WT_Env ρC1)].[va1 : Expr/].
    set (plug c e1).[subst_of_WT_Env (extend_WT_Env ρC1 va1)].
    assert (y = y0) by (subst y y0; autosubst).
    rewrite (μ_rewrite
               H0 τr
               (ty_subst1 va1 Hplug1)
               (close (extend_WT_Env ρC1 va1) (tc_ctx_of_tc He1 HC))).
    repeat subst.
    clear H0.
    auto.
  }
Qed.

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
  Transparent π.
  induction n. {
    unfold π.
    apply πL_same_integral.
  } {
    rewrite <- IHn.
    clear IHn.
    replace (f ∘ π (S n)) with (f ∘ π n ∘ πR) by auto.
    apply πR_same_integral.
  }
  Opaque π.
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
  Transparent π.
  simpl.
  rewrite πR_join.
  rewrite πL_join.
  auto.
  Opaque π.
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

Lemma break_right {e1 e2}
    (He1 : (TC nil ⊢ e1 : ℝ))
    (He2 : (TC nil ⊢ e2 : ℝ))
    σ A :
  eval_in (tc_right He1 He2) A σ =
  option0 (plus_in A <$> ev He1 (π 0 σ) <*> ev He2 (π 1 σ))
          [*] ew He1 (π 0 σ)
          [*] ew He2 (π 1 σ).
Proof.
  intros.
  unfold eval_in.
  unfold ev at 1, ew at 1.
  decide_eval _ as [v0 w0 ex0 u0]. {
    inversion ex0; subst; try absurd_Val.
    unfold ev, ew.
    simpl.

    decide_eval He1 as [v3 w3 ex3 u3].
    pose proof big_preservation He1 ex3.
    destruct v3 using Val_rect; inversion X1; subst.

    decide_eval He2 as [v5 w5 ex5 u5].
    pose proof big_preservation He2 ex5.
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
    decide_eval He1 as [v3 w3 ex3 u3].
    decide_eval He2 as [v4 w4 ex4 u4].
    contradict not_ex.

    pose proof big_preservation He1 ex3.
    destruct v3 using Val_rect; inversion X; subst.

    pose proof big_preservation He2 ex4.
    destruct v4 using Val_rect; inversion X0; subst.

    eexists (v_real (r + r0) : Val, w3 [*] w4).
    econstructor; eauto.
  }
Qed.

Lemma break_left {e1 e2}
      (He1 : (TC nil ⊢ e1 : ℝ))
      (He2 : (TC nil ⊢ e2 : ℝ))
      σ A :
  let σe1 := (π 0 (π 2 σ)) in
  let σe2 := (π 1 σ) in
  eval_in (tc_left He1 He2) A σ =
  option0 (plus_in A <$> ev He1 σe1 <*> ev He2 σe2)
          [*] ew He1 σe1
          [*] ew He2 σe2.
Proof.
  intros.

  Opaque π.

  unfold eval_in.
  unfold ev at 1, ew at 1.
  decide_eval _ as [v0 w0 ex0 u0]. {
    pose proof big_preservation (tc_left He1 He2) ex0.
    destruct v0 using Val_rect; inversion X; subst.
    inversion ex0; subst; try absurd_Val.
    inversion X0; subst.
    inversion H0; subst.
    dependent destruction X2.
    simpl in *.
    destruct is_v0, is_v1.

    replace (e1.[ren S].[v1 : Expr/]) with e1 in * by autosubst.

    unfold ev, ew.

    decide_eval He1 as [v4 w4 ex4 u4].
    pose proof big_preservation He1 ex4.
    destruct v4 using Val_rect; inversion X2; subst.

    decide_eval He2 as [v5 w5 ex5 u5].
    pose proof big_preservation He2 ex5.
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
    decide_eval He1 as [v4 w4 ex4 u4].
    pose proof big_preservation He1 ex4.
    destruct v4 using Val_rect; inversion X; subst.

    decide_eval He2 as [v5 w5 ex5 u5].
    pose proof big_preservation He2 ex5.
    destruct v5 using Val_rect; inversion X0; subst.

    contradict not_ex.
    eexists (v_real (r + r0) : Val, _).
    eapply EApp; eauto. {
      eapply EPure'.
      reflexivity.
    } {
      simpl.
      replace (e1.[ren S].[e_real r0/]) with e1 in * by autosubst.
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
  Transparent π.
  unfold kajigger.
  simpl.
  rewrite πR_join.
  rewrite πL_join.
  auto.
  Opaque π.
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

Lemma beta_addition e1 e2 :
  (TC · ⊢ e1 : ℝ) ->
  (TC · ⊢ e2 : ℝ) ->
  (EXP · ⊢ ex_left e1 e2 ≈ ex_right e1 e2 : ℝ).
Proof.
  intros He1 He2.

  refine (mk_related_exprs (tc_left He1 He2) (tc_right He1 He2) _).
  simpl.
  intros.

  destruct ρ0 as [ρ0 Hρ0].
  destruct ρ1 as [ρ1 Hρ1].
  dependent destruction Hρ0.
  dependent destruction Hρ1.
  clear Hρ.
  unfold subst_of_WT_Env, downgrade_env.
  simpl.

  hnf.
  rewrite subst_comp, 2 subst_id.
  do 2 eexists.
  shelve.
  Unshelve. {
    repeat econstructor; eauto.
    apply (ty_ren He1).
    auto.
  } {
    constructor; auto.
  }

  intros.

  replace (TCPlus He1 He2) with (tc_right He1 He2) by apply tc_unique.
  replace (TCApp _ _) with (tc_left He1 He2) by apply tc_unique.
  unfold μ.

  symmetry.
  rewrite (int_inj_entropy _ kajigger_n_inj).
  symmetry.
  rewrite kajigger_equiv.

  setoid_rewrite break_left.
  setoid_rewrite break_right.

  f_equal.
  extensionality σ.
  unfold compose.

  rewrite kajigger_1.
  rewrite kajigger_02.
  do 3 f_equal.
  unfold plus_in.
  destruct (ev _ _); simpl; auto.
  destruct (ev _ _); simpl; auto.
  destruct (Val_e _); auto.
  destruct (Val_e _); auto.
  f_equal.
  unfold Indicator.
  f_equal.
  apply H.
  reflexivity.
Qed.
