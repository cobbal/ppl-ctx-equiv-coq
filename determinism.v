Require Import Reals.
Require Import List.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import Coq.fourier.Fourier.
Require Import nnr.
Require Import syntax.
Require Import utils.
Require Import micromega.Lia.

Import EqNotations.

Local Open Scope R.

Definition dE_rel' τ (dV_rel_τ : val τ -> Type) (e : expr · τ) : Type :=
  forall σ,
    (existsT (vw : val τ * R+),
     let (v, w) := vw in
     (dV_rel_τ v)
       ⨉ (EVAL σ ⊢ e ⇓ v, w)
       ⨉ (forall v' w', (EVAL σ ⊢ e ⇓ v', w') -> (v, w) = (v', w'))
    ) +
    ((existsT vw : (val τ * R+), let (v, w) := vw in EVAL σ ⊢ e ⇓ v, w) -> False).

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
    lookup Γ x = Some τ ->
    dep_lookup ρ x = Some (existT _ τ v) ->
    dV_rel τ v.
Proof.
  intros.
  revert Γ ρ H H0 X.
  induction x; intros. {
    destruct ρ; inversion H; subst.
    simpl in *.
    dependent destruction H0.
    destruct X.
    auto.
  } {
    destruct ρ; inversion H; subst.
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
  exists (v_real r, nnr_1).
  repeat constructor. {
    apply EPure'.
    destruct close; simpl in *.
    apply erase_injective.
    auto.
  } {
    intros.
    destruct close; simpl in *.
    dependent destruction H.
    destruct_val v'.
    inversion e.
    auto.
  }
Qed.

Lemma compat_var Γ x τ Hx :
  related_expr Γ τ (e_var x Hx).
Proof.
  left.

  destruct (env_search ρ Hx) as [v ρv].
  exists (v, nnr_1).
  repeat constructor; auto. {
    eapply apply_dG_rel; eauto.
  } {
    apply EPure'.
    destruct close; simpl in *.
    apply lookup_subst in ρv.
    elim_erase_eqs.
    auto.
  } {
    intros.
    destruct close; simpl in *.
    apply lookup_subst in ρv.
    elim_erase_eqs.

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

  exists (v_lam (proj1_sig (body_subst ρ body)), nnr_1).
  constructor; [constructor |]. {
    constructor.
    intros.
    destruct ty_subst1; simpl in *.

    specialize (Hbody _ (extend_dgrel X Hρ)).

    destruct close, body_subst; simpl in *.
    replace x0 with x in Hbody; auto.
    apply erase_injective.

    rewrite e, e0, e1.
    autosubst.
  } {
    apply EPure'.

    apply erase_injective.
    destruct close, body_subst; simpl in *.
    rewrite e, e0.
    auto.
  } {
    intros.
    destruct close, body_subst; simpl in *.
    assert (is_val x). {
      simpl.
      rewrite e.
      exact I.
    }
    change (EVAL σ ⊢ mk_val x H0 ⇓ v', w') in H.
    destruct (invert_eval_val H); subst.
    f_equal.

    d_destruct (x, e).
    elim_erase_eqs.

    destruct H0.
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

  repeat destruct close; simpl in *.
  destruct x1; inversion e1.
  elim_erase_eqs.

  destruct Hef as [[[vf wf] [[Hvf EVAL_f] uf]] | not_ex]. {
    destruct Hea as [[[va wa] [[Hva EVAL_a] ua]] | not_ex]. {
      destruct_val vf.
      destruct Hvf as [body0 Hvf].
      clear body.

      destruct (Hvf va Hva (π 2 σ)) as [[[vr wr] [[Hvr EVAL_r] ur]] | not_ex]. {
        left.
        exists (vr, wf [*] wa [*] wr).

        repeat econstructor; eauto.
        intros.
        d_destruct H; try absurd_val.


        specialize (uf _ _ H).
        specialize (ua _ _ H2).
        d_destruct (uf, ua).

        specialize (ur _ _ H3).
        d_destruct ur.

        reflexivity.
      } {
        right.
        intros.
        contradict not_ex.
        destruct X as [[? ?] ?].

        d_destruct y; try absurd_val.

        specialize (uf _ _ y1).
        specialize (ua _ _ y2).
        d_destruct (uf, ua).

        eexists (_, _); eauto.
      }
    } {
      right.
      intros.
      contradict not_ex.
      destruct X as [[? ?] ?].

      d_destruct y; try absurd_val.

      eexists (_, _); eauto.
    }
  } {
    right.
    intros.
    contradict not_ex.
    destruct X as [[? ?] ?].

    d_destruct y; try absurd_val.

    eexists (_, _); eauto.
  }
Qed.

Lemma compat_factor Γ e :
  related_expr Γ ℝ e ->
  related_expr Γ ℝ (e_factor e).
Proof.
  intros He ? ? ?.

  specialize (He ρ Hρ σ).

  repeat destruct close; simpl in *.
  d_destruct (x0, e1).
  elim_erase_eqs.

  destruct He as [[[v w] [[Hv EVAL_e] u]] | not_ex]. {
    destruct_val v.

    destruct (Rle_dec 0 r). {
      left.
      exists (v_real r, mknnr r r0 [*] w).
      repeat econstructor; eauto.
      intros.
      d_destruct H; try absurd_val.

      specialize (u _ _ H).
      d_destruct u.
      f_equal.
      nnr.
    } {
      right.
      intros.

      destruct X as [[? ?] ?].

      d_destruct y; try absurd_val.
      specialize (u _ _ y).
      d_destruct u.
      contradiction rpos.
    }
  } {
    right.
    intros.
    contradict not_ex.

    destruct X as [[? ?] ?].
    d_destruct y; try absurd_val.
    eexists (_, _); eauto.
  }
Qed.

Lemma compat_sample Γ :
  related_expr Γ ℝ e_sample.
Proof.
  intros ? ? ?.
  left.

  destruct close; simpl in *.
  d_destruct (x, e).

  eexists (_, _).
  repeat econstructor; eauto.
  intros.

  d_destruct H; try absurd_val.
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

  repeat destruct close; simpl in *.
  d_destruct (x1, e1).
  elim_erase_eqs.

  destruct Hel as [[[vl wl] [[Hvl EVAL_l] ul]] | not_ex]. {
    destruct Her as [[[vr wr] [[Hvr EVAL_r] ur]] | not_ex]. {
      left.
      destruct_val vl.
      destruct_val vr.

      exists (v_real (r + r0), wl [*] wr).
      repeat econstructor; eauto.
      intros.

      d_destruct H; try absurd_val.

      specialize (ul _ _ H).
      specialize (ur _ _ H0).
      d_destruct (ul, ur).
      auto.
    } {
      right.
      intros.

      contradict not_ex.

      destruct X as [[? ?] ?].
      d_destruct y; try absurd_val.

      eexists (_, _); eauto.
    }
  } {
    right.
    intros.

    contradict not_ex.

    destruct X as [[? ?] ?].
    d_destruct y; try absurd_val.

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

Theorem eval_dec {τ} (e : expr · τ) σ :
  (existsT! vw : (val τ * R+), let (v, w) := vw in EVAL σ ⊢ e ⇓ v, w) +
  ((existsT vw : (val τ * R+), let (v, w) := vw in EVAL σ ⊢ e ⇓ v, w) -> False).
Proof.
  pose proof (fundamental_property e dep_nil I) as fp.

  destruct close; simpl in *.
  rewrite subst_id in e0.
  apply erase_injective in e0.
  subst.

  destruct (fp σ); [left | right; auto]. {
    destruct s as [[v w] [[? ?] ?]].
    exists (v, w).
    split; auto.
    intro.
    destruct x'.
    apply e1.
  }
Qed.
