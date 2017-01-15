(** This file is very boring. It simply says that our language is deterministic,
    and we could have written evaluation as a parital function if our
    implementation language allowed general recursion.

    ----

    The only exports of interest from this file will be contained in the module
    [eval_dec] at the very bottom. *)

Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.

Require Import utils.
Require Import syntax.

Local Open Scope ennr.

Definition dE_rel' τ (dV_rel_τ : val τ -> Type) (e : expr · τ) : Type :=
  forall σ,
    {vw : (val τ * R+) &
          let (v, w) := vw in
          (dV_rel_τ v
           * (EVAL σ ⊢ e ⇓ v, w)
           * (forall v' w', (EVAL σ ⊢ e ⇓ v', w') -> v' = v /\ w' = w))%type
    } +
    ({vw : (val τ * R+) &
           let (v, w) := vw in EVAL σ ⊢ e ⇓ v, w}
     -> False).

Definition dV_rel_real (v : val ℝ) : Type := True.

Inductive dV_rel_arrow {τa τr}
          (dV_rel_a : val τa -> Type)
          (dV_rel_r : val τr -> Type)
  : val (τa ~> τr) -> Type :=
| mk_dV_rel_arrow
    (body : expr (τa :: ·) τr) :
    (forall va,
        dV_rel_a va ->
        dE_rel' τr dV_rel_r (proj1_sig (ty_subst1 body va))) ->
    dV_rel_arrow dV_rel_a dV_rel_r (v_lam body).

Fixpoint dV_rel τ : val τ -> Type :=
  match τ with
  | ℝ => dV_rel_real
  | (τa ~> τr) => @dV_rel_arrow _ _ (dV_rel τa) (dV_rel τr)
  end.

Hint Unfold dV_rel dV_rel_real.
Hint Constructors dV_rel_arrow.

Definition dE_rel τ := dE_rel' τ (dV_rel τ).

Definition dG_rel Γ (ρ : wt_env Γ) : Type :=
  dep_env_allT dV_rel ρ.

Lemma apply_dG_rel {Γ ρ} :
  dG_rel Γ ρ ->
  forall x τ (v : val τ),
    erase v = erase_wt_env ρ x ->
    dV_rel τ v.
Proof.
  intros.
  revert Γ ρ H X.
  induction x; intros. {
    dep_destruct ρ. {
      destruct_val v; subst; discriminate.
    }
    destruct X.
    cbn in H.
    pose proof (expr_type_unique _ _ H).
    subst.
    elim_erase_eqs.
    apply val_eq in H.
    subst.
    auto.
  } {
    dep_destruct ρ. {
      destruct_val v; subst; discriminate.
    }
    simpl in *.
    eapply IHx; eauto.
    destruct X.
    auto.
  }
Qed.

Lemma extend_dgrel {Γ τ ρ v} :
  (dV_rel τ v) ->
  (dG_rel Γ ρ) ->
  (dG_rel (τ :: Γ) (dep_cons v ρ)).
Proof.
  constructor; auto.
Qed.

Definition related_expr Γ τ (e : expr Γ τ) : Type :=
  forall ρ (Hρ : dG_rel Γ ρ),
    dE_rel τ (proj1_sig (close ρ e)).

Lemma compat_real Γ r :
  related_expr Γ ℝ (e_real r).
Proof.
  left.
  exists (v_real r, 1).

  elim_sig_exprs.

  split; [repeat constructor |]. {
    elim_erase_eqs.
    rewrite rewrite_v_real.
    apply EVAL_val.
  } {
    intros.
    destruct_val v'.
    dep_destruct H.
    auto.
  }
Qed.

Lemma compat_var Γ x τ Hx :
  related_expr Γ τ (e_var x Hx).
Proof.
  left.

  destruct (env_search_subst ρ Hx) as [v ?].
  exists (v, 1).

  elim_sig_exprs.
  elim_erase_eqs.

  split; [repeat constructor |]; auto. {
    eapply apply_dG_rel; eauto.
  } {
    intros.
    destruct (invert_eval_val H); subst.
    auto.
  }
Qed.

Lemma compat_lam Γ τa τr body :
  related_expr (τa :: Γ) τr body ->
  related_expr Γ (τa ~> τr) (e_lam body).
Proof.
  intros Hbody.
  left.

  elim_sig_exprs.
  dep_destruct (e, He).

  exists (v_lam e, 1).
  constructor; [constructor |]. {
    constructor.
    intros.

    specialize (Hbody _ (extend_dgrel X Hρ)).
    elim_sig_exprs.
    rewrite x in He1.
    asimpl in He1.
    elim_erase_eqs.

    exact Hbody.
  } {
    rewrite rewrite_v_lam.
    apply EVAL_val.
  } {
    intros.
    change (EVAL σ ⊢ v_lam e ⇓ v', w') in H.
    destruct (invert_eval_val H); subst.
    simpl.
    auto.
  }
Qed.

Lemma compat_app Γ τa τr ef ea :
  related_expr Γ (τa ~> τr) ef ->
  related_expr Γ τa ea ->
  related_expr Γ τr (e_app ef ea).
Proof.
  intros Hef Hea ? ? ?.

  specialize (Hef ρ Hρ (π 0 σ)).
  specialize (Hea ρ Hρ (π 1 σ)).

  elim_sig_exprs.
  dep_destruct (e1, He1).
  elim_erase_eqs.

  destruct Hef as [[[vf wf] [[Hvf EVAL_f] uf]] | not_ex]. {
    destruct Hea as [[[va wa] [[Hva EVAL_a] ua]] | not_ex]. {
      destruct_val vf.
      destruct Hvf as [body0 Hvf].
      clear body.

      destruct (Hvf va Hva (π 2 σ)) as [[[vr wr] [[Hvr EVAL_r] ur]] | not_ex]. {
        left.
        exists (vr, wf * wa * wr).

        constructor; [repeat econstructor |]; eauto.
        intros.
        dep_destruct H; try absurd_val.

        destruct (uf _ _ H).
        destruct (ua _ _ H0); subst.
        dep_destruct H2.

        destruct (ur _ _ H1); subst.
        auto.
      } {
        right.
        intros.
        contradict not_ex.
        destruct X as [[? ?] ?].

        dep_destruct y; try absurd_val.

        destruct (uf _ _ y1).
        destruct (ua _ _ y2); subst.
        dep_destruct H.

        eexists (_, _); eauto.
      }
    } {
      right.
      intros.
      contradict not_ex.
      destruct X as [[? ?] ?].

      dep_destruct y; try absurd_val.

      eexists (_, _); eauto.
    }
  } {
    right.
    intros.
    contradict not_ex.
    destruct X as [[? ?] ?].

    dep_destruct y; try absurd_val.

    eexists (_, _); eauto.
  }
Qed.

Lemma compat_factor Γ e :
  related_expr Γ ℝ e ->
  related_expr Γ ℝ (e_factor e).
Proof.
  intros He ? ? ?.

  specialize (He ρ Hρ σ).

  elim_sig_exprs.
  dep_destruct (e1, He1).
  elim_erase_eqs.

  destruct He as [[[v w] [[Hv EVAL_e] u]] | not_ex]. {
    destruct_val v.

    destruct (Rle_dec 0 r). {
      left.
      exists (v_real r, finite r r0 * w).
      constructor; [repeat econstructor |]; eauto.
      intros.
      dep_destruct H; try absurd_val.

      destruct (u _ _ H); subst.
      dep_destruct H0.
      split; auto.
      f_equal.
      Finite.
    } {
      right.
      intros.

      destruct X as [[? ?] ?].

      dep_destruct y; try absurd_val.
      destruct (u _ _ y); subst.
      dep_destruct H.
      contradiction rpos.
    }
  } {
    right.
    intros.
    contradict not_ex.

    destruct X as [[? ?] ?].
    dep_destruct y; try absurd_val.
    eexists (_, _); eauto.
  }
Qed.

Lemma compat_sample Γ :
  related_expr Γ ℝ e_sample.
Proof.
  intros ? ? ?.
  left.

  elim_sig_exprs.
  dep_destruct (e, He).

  eexists (_, _).
  constructor; [repeat econstructor |]; eauto.
  intros.

  dep_destruct H; try absurd_val.
  simpl.
  auto.
Qed.

Lemma compat_plus Γ el er :
  related_expr Γ ℝ el ->
  related_expr Γ ℝ er ->
  related_expr Γ ℝ (e_plus el er).
Proof.
  intros Hel Her ? ? ?.

  specialize (Hel ρ Hρ (π 0 σ)).
  specialize (Her ρ Hρ (π 1 σ)).

  elim_sig_exprs.
  dep_destruct (e1, He1).
  elim_erase_eqs.

  destruct Hel as [[[vl wl] [[Hvl EVAL_l] ul]] | not_ex]. {
    destruct Her as [[[vr wr] [[Hvr EVAL_r] ur]] | not_ex]. {
      left.
      destruct_val vl.
      destruct_val vr.

      exists (v_real (r + r0), wl * wr).
      constructor; [repeat econstructor |]; eauto.
      intros.

      dep_destruct H; try absurd_val.

      destruct (ul _ _ H); subst.
      destruct (ur _ _ H0); subst.
      inject H1.
      inject H2.

      split; auto.
    } {
      right.
      intros.

      contradict not_ex.

      destruct X as [[? ?] ?].
      dep_destruct y; try absurd_val.

      eexists (_, _); eauto.
    }
  } {
    right.
    intros.

    contradict not_ex.

    destruct X as [[? ?] ?].
    dep_destruct y; try absurd_val.

    eexists (_, _); eauto.
  }
Qed.

Lemma fundamental_property {Γ τ} e :
  related_expr Γ τ e.
Proof.
  induction e.
  - apply compat_real.
  - apply compat_var; auto.
  - apply compat_lam; auto.
  - eapply compat_app; eauto.
  - eapply compat_factor; eauto.
  - apply compat_sample; auto.
  - eapply compat_plus; eauto.
Qed.

Module eval_dec.
  Inductive eval_dec_result {τ} (e : expr · τ) (σ : Entropy) :=
  | eval_dec_ex_unique
      (v : val τ) (w : R+) (ev : EVAL σ ⊢ e ⇓ v, w)
      (u : forall v' w',
          (EVAL σ ⊢ e ⇓ v', w') ->
          v' = v /\ w' = w)
  | eval_dec_not_ex
      (not_ex : forall v w,
          (EVAL σ ⊢ e ⇓ v, w) ->
          False)
  .
  Arguments eval_dec_ex_unique {_ _ _} v w _ _.
  Arguments eval_dec_not_ex {_ _ _} not_ex.

  Theorem eval_dec {τ} (e : expr · τ) σ : eval_dec_result e σ.
  Proof.
    pose proof (fundamental_property e dep_nil I) as fp.

    elim_sig_exprs.
    elim_erase_eqs.

    destruct (fp σ). {
      destruct s as [[v w] [[? ?] ?]].
      eapply eval_dec_ex_unique; eauto.
    } {
      apply eval_dec_not_ex.
      intros.
      contradict f.
      exists (v, w).
      auto.
    }
  Qed.
End eval_dec.