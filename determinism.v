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

Local Open Scope R.

Definition dE_rel' (τ : Ty) (dV_rel_τ : Val -> Type) (c : Config τ) : Type :=
  let (Γ, ρ, Hρ, e, He) := c in
  forall σ,
    (existsT (vw : Val * R+),
     let (v, w) := vw in
     (dV_rel_τ v)
       ⨉ (EVAL ρ, σ ⊢ e ⇓ v, w)
       ⨉ (forall v' w', (EVAL ρ, σ ⊢ e ⇓ v', w') -> (v, w) = (v', w'))
    ) +
    ((existsT vw : (Val * R+), let (v, w) := vw in EVAL ρ, σ ⊢ e ⇓ v, w) -> False).

Definition dV_rel_real (v : Val) : Type :=
  match v with
  | v_real _ => True
  | _ => False
  end.

Definition dV_rel_arrow
       (τa τr : Ty) (dV_rel_a dV_rel_r : Val -> Type)
       (v : Val)
  : Type
  := match v with
     | v_clo τa' body ρ_clo =>
       (τa = τa') ⨉
       { Γ_clo : Env Ty &
       { Hρ_clo : (TCEnv ⊢ ρ_clo : Γ_clo) &
       { tc_body : (TC (extend Γ_clo τa) ⊢ body : τr) &
        forall {va : WT_Val τa} (Hva : dV_rel_a va),
          (dE_rel' τr dV_rel_r (mk_config (tc_env_extend Hρ_clo va) tc_body))
       }}}
     | _ => False
     end.

Reserved Notation "'dVREL' v ∈ V[ τ ]"
         (at level 69, v at level 99, τ at level 99).
Fixpoint dV_rel τ : Val -> Type :=
  match τ with
  | ℝ => dV_rel_real
  | (τa ~> τr) => dV_rel_arrow τa τr (dV_rel τa) (dV_rel τr)
  end.

Hint Unfold dV_rel dV_rel_real dV_rel_arrow.

Definition dE_rel τ := dE_rel' τ (dV_rel τ).

(* Notation "'dVREL' v ∈ V[ τ ]" := (dV_rel τ v). *)

(* Notation "'dEREL' e ∈ E[ τ ]" := *)
(*   (dE_rel τ (dV_rel τ) e) *)
(*     (at level 69, e at level 99, τ at level 99). *)

Record dG_rel {Γ : Env Ty} {ρ : Env Val} : Type :=
  {
    dG_rel_modeling : (TCEnv ⊢ ρ : Γ);
    dG_rel_V : forall {x v τ},
                     lookup Γ x = Some τ ->
                     lookup ρ x = Some v ->
                     dV_rel τ v
  }.
Arguments dG_rel _ _ : clear implicits.

(* Notation "'dGREL' ρ ∈ G[ Γ ]" := *)
(*   (dG_rel Γ ρ) *)
(*     (at level 69, ρ at level 99, Γ at level 99). *)

Lemma tc_of_dV_rel {τ v} :
  dV_rel τ v ->
  (TCV ⊢ v : τ).
Proof.
  intros.
  destruct τ, v; simpl in *; try tauto. {
    constructor.
  } {
    destruct X as [? [? [? [? ?]]]].
    subst.
    econstructor; eauto.
  }
Qed.

Lemma extend_dgrel {Γ ρ v τ} :
  (dG_rel Γ ρ) ->
  (dV_rel τ v) ->
  (dG_rel (extend Γ τ) (extend ρ v)).
Proof.
  intros.
  split. {
    constructor. {
      apply X.
    } {
      apply tc_of_dV_rel.
      auto.
    }
  } {
    intros.
    induction x. {
      simpl in *.
      inversion H0.
      inversion H.
      subst.
      auto.
    } {
      destruct X as [_ X].
      apply (X x); auto.
    }
  }
Qed.

Definition related_expr (Γ : Env Ty) (e : Expr) (τ : Ty) : Type :=
  {He : (TC Γ ⊢ e : τ) &
        forall {ρ} (Hρ : dG_rel Γ ρ),
          (dE_rel τ (mk_config (dG_rel_modeling Hρ) He))}.

Lemma compat_real Γ r :
  related_expr Γ (e_pure (e_real r)) ℝ.
Proof.
  exists (TCReal _).
  intros ρ Hρ σ.
  left.
  exists (v_real r, nnr_1).
  repeat constructor.
  intros.
  inversion X; subst.
  f_equal.
  inversion H0.
  reflexivity.
Qed.

Lemma compat_var Γ x τ :
  lookup Γ x = Some τ ->
  related_expr Γ (e_pure (e_var x)) τ.
Proof.
  intros Γτ.
  exists (TCVar Γτ).
  intros ρ Hρ σ.
  left.

  pose proof (dG_rel_modeling Hρ).

  destruct (env_search X Γτ) as [v ρv].
  exists (v : Val, nnr_1).
  repeat constructor; auto. {
    eapply (dG_rel_V Hρ); eauto.
  } {
    intros.
    inversion X0; subst.
    f_equal.
    inversion H0.
    rewrite ρv in *.
    inversion H1.
    reflexivity.
  }
Qed.

Lemma compat_lam Γ body τa τr :
  related_expr (extend Γ τa) body τr ->
  related_expr Γ (e_pure (e_lam τa body)) (τa ~> τr).
Proof.
  intros Hbody.
  destruct Hbody as [tc_body Hbody].
  exists (TCLam tc_body).
  intros ρ Hρ σ.
  left.
  exists (v_clo τa body ρ, nnr_1).
  constructor; [constructor |]. {
    simpl.
    split; auto.
    exists Γ.
    exists (dG_rel_modeling Hρ).
    exists tc_body.
    intros.
    apply (Hbody _ (extend_dgrel Hρ Hva)).
  } {
    constructor.
    auto.
  } {
    intros.
    inversion X; subst.
    f_equal.
    inversion H0.
    reflexivity.
  }
Qed.

Lemma compat_app Γ ef ea τa τr :
  related_expr Γ ef (τa ~> τr) ->
  related_expr Γ ea τa ->
  related_expr Γ (e_app ef ea) τr.
Proof.
  intros Hef Hea.
  destruct Hef as [tc_ef Hef].
  destruct Hea as [tc_ea Hea].
  exists (TCApp tc_ef tc_ea).
  intros ρ Hρ σ.

  specialize (Hef ρ Hρ (π 0 σ)).
  specialize (Hea ρ Hρ (π 1 σ)).

  destruct Hef as [[[vf wf] [[Hvf EVAL_f] uf]] | not_ex]. {
    destruct Hea as [[[va wa] [[Hva EVAL_a] ua]] | not_ex]. {
      destruct vf as [| τa' body ρ_clo]; [inversion Hvf; contradiction |].
      destruct Hvf as [? [Γ_clo [Hρ_clo [tc_body Hvf]]]]; simpl in Hvf.
      subst τa'.
      pose (wt_va := mk_WT_Val (tc_of_dV_rel Hva)).
      destruct (Hvf wt_va Hva (π 2 σ)) as [[[vr wr] [[Hvr EVAL_r] ur]] | not_ex]. {
        left.
        exists (vr, wf [*] wa [*] wr).
        repeat econstructor; eauto.
        intros.
        inversion X; subst.

        specialize (uf _ _ X0).
        specialize (ua _ _ X1).
        inversion uf.
        inversion ua.
        subst.

        specialize (ur _ _ X2).
        inversion ur.
        subst.

        reflexivity.
      } {
        right.
        intros.
        apply not_ex.
        destruct X as [[? ?] ?].
        inversion y; subst.

        specialize (uf _ _ X).
        specialize (ua _ _ X0).
        inversion uf.
        inversion ua.
        subst.

        eexists (_, _); eauto.
      }
    } {
      right.
      intros.
      apply not_ex.
      destruct X as [[? ?] ?].
      inversion y; subst.

      eexists (_, _); eauto.
    }
  } {
    right.
    intros.
    apply not_ex.
      destruct X as [[? ?] ?].
      inversion y; subst.

      eexists (_, _); eauto.
  }
Qed.

Lemma compat_factor Γ e :
  related_expr Γ e ℝ ->
  related_expr Γ (e_factor e) ℝ.
Proof.
  intros He.
  destruct He as [tc_e He].
  exists (TCFactor tc_e).
  intros ρ Hρ σ.

  specialize (He ρ Hρ σ).

  destruct He as [[[v w] [[Hv EVAL_e] u]] | not_ex]. {
    destruct v; try contradiction.
    destruct (Rle_dec 0 r). {
      left.
      exists (v_real r, mknnr r r0 [*] w).
      repeat constructor; eauto.
      intros.
      inversion X.
      subst.

      specialize (u _ _ X0).
      inversion u; subst.
      do 2 f_equal.
      nnr; simpl; auto.
    } {
      right.
      intros.

      destruct X as [[? ?] ?].
      inversion y; subst.

      specialize (u _ _ X).
      inversion u; subst.

      tauto.
    }
  } {
    right.
    intros.
    apply not_ex.

    destruct X as [[? ?] ?].
    inversion y; subst.
    eexists (_, _).
    exact X.
  }
Qed.

Lemma compat_sample Γ :
  related_expr Γ e_sample ℝ.
Proof.
  exists TCSample.
  left.
  eexists (_, _); repeat constructor; simpl; auto.

  intros.
  inversion X.
  auto.
Qed.

Lemma compat_plus Γ el er :
  related_expr Γ el ℝ ->
  related_expr Γ er ℝ ->
  related_expr Γ (e_plus el er) ℝ.
Proof.
  intros Hel Her.
  destruct Hel as [tc_el Hel].
  destruct Her as [tc_er Her].
  exists (TCPlus tc_el tc_er).
  intros ρ Hρ σ.

  specialize (Hel ρ Hρ (π 0 σ)).
  specialize (Her ρ Hρ (π 1 σ)).

  destruct Hel as [[[vl wl] [[Hvl EVAL_l] ul]] | not_ex]. {
    destruct Her as [[[vr wr] [[Hvr EVAL_r] ur]] | not_ex]. {
      left.
      destruct vl, vr; try (destruct Hvl, Hvr; contradiction).
      exists (v_real (r + r0), wl [*] wr).
      repeat constructor; auto.

      intros.
      inversion X; subst.

      specialize (ul _ _ X0).
      specialize (ur _ _ X1).
      inversion ul.
      inversion ur.
      subst.
      auto.
    } {
      right.
      intros.
      destruct X as [[? ?] ?].
      inversion y; subst.

      contradict not_ex.
      eexists (_, _); eauto.
    }
  } {
    right.
    intros.
    destruct X as [[? ?] ?].
    inversion y; subst.

    contradict not_ex.
    eexists (_, _); eauto.
  }
Qed.

Lemma fundamental_property {Γ e τ} :
  (TC Γ ⊢ e : τ) ->
  related_expr Γ e τ.
Proof.
  intros tc.
  induction tc.
  - apply compat_real.
  - apply compat_var; auto.
  - apply compat_lam; auto.
  - eapply compat_app; eauto.
  - eapply compat_factor; eauto.
  - apply compat_sample; auto.
  - eapply compat_plus; eauto.
Qed.

Lemma fundamental_environment {Γ ρ} :
  (TCEnv ⊢ ρ : Γ) ->
  (dG_rel Γ ρ).
Proof.
  intros Hρ.

  induction Hρ using tc_env_val_rect
  with (P := fun v τ Hv => dV_rel τ v). {
    intros.
    repeat constructor.
  } {
    intros.
    split; auto.
    exists Γ_clo.
    exists Hρ.
    exists t.
    intros.
    pose proof fundamental_property t.
    destruct X.
    refine (d _ _).
    apply extend_dgrel; auto.
  } {
    repeat constructor.
    intros.
    destruct x; discriminate H.
  } {
    intros.
    repeat constructor; auto.
    intros.

    destruct x; simpl in *. {
      inversion H.
      inversion H0.
      subst.
      auto.
    } {
      eapply IHHρ; eauto.
    }
  }
Qed.

Theorem eval_dec :
  forall {Γ ρ e τ},
    (TCEnv ⊢ ρ : Γ) ->
    (TC Γ ⊢ e : τ) ->
    forall σ,
      (existsT! vw : (Val * R+), let (v, w) := vw in EVAL ρ, σ ⊢ e ⇓ v, w) +
      ((existsT vw : (Val * R+), let (v, w) := vw in EVAL ρ, σ ⊢ e ⇓ v, w) -> False).
Proof.
  intros.
  destruct (fundamental_property H).
  specialize (d ρ (fundamental_environment X) σ).
  destruct d; [| right; auto].

  left.
  destruct s as [[v w] [[? ?] ?]].
  exists (v, w).
  split; auto.
  intro.
  destruct x'.
  apply e1.
Qed.

Theorem big_preservation :
  forall {Γ ρ e τ v w σ},
    (TCEnv ⊢ ρ : Γ) ->
    (TC Γ ⊢ e : τ) ->
    (EVAL ρ, σ ⊢ e ⇓ v, w) ->
    (TCV ⊢ v : τ).
Proof.
  intros.
  destruct (fundamental_property H).
  specialize (d ρ (fundamental_environment X) σ).
  destruct d. {
    destruct s as [[v' w'] [[? ?] ?]].
    specialize (e1 v w X0).
    inversion e1; subst.
    apply tc_of_dV_rel; auto.
  } {
    contradict f.
    eexists (_, _); eauto.
  }
Qed.
