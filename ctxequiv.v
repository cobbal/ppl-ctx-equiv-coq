Require Import utils.
Require Import syntax.
Require Import relations.
Require Import micromega.Lia.
Require Import List.

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

Definition ctx_equiv {Γ τ e0 e1}
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
    ctx_equiv He0 He1.
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