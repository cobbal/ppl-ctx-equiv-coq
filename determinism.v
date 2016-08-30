Require Import Reals.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics.
Require Import Coq.fourier.Fourier.
Require Import nnr.
Require Import syntax.
Require Import utils.

Local Open Scope R.

Definition dE_rel (dV_rel : Ty -> Val -> Type) (τ : Ty) (c : Config) : Type :=
  let (ρ, e) := c in
  forall σ,
    (existsT (vw : Val * R+),
     let (v, w) := vw in
     (dV_rel τ v)
       ⨉ (EVAL ρ, σ ⊢ e ⇓ v, w)
       ⨉ (forall v' w', (EVAL ρ, σ ⊢ e ⇓ v', w') -> (v, w) = (v', w'))
    ) +
    ((existsT vw : (Val * R+), let (v, w) := vw in EVAL ρ, σ ⊢ e ⇓ v, w) -> False).

Reserved Notation "'dVREL' v ∈ V[ τ ]"
         (at level 69, v at level 99, τ at level 99).
Fixpoint dV_rel τ v : Type :=
  match τ with
  | ℝ => match v with
         | v_real _ => True
         | _ => False
         end
  | τa ~> τr => match v with
                | v_clo x e ρ =>
                  forall {va},
                    dV_rel τa va ->
                    dE_rel dV_rel τr (ρ[x → va], e)
                | _ => False
                end
  end
where "'dVREL' v ∈ V[ τ ]" := (dV_rel τ v)
.

Notation "'dEREL' e ∈ E[ τ ]" :=
  (dE_rel dV_rel τ e)
    (at level 69, e at level 99, τ at level 99).

Record dG_rel {Γ : Env Ty} {ρ : Env Val} : Type :=
  {
    dG_rel_modeling : (ENV ρ ⊨ Γ);
    dG_rel_V : forall {x v τ},
                     Γ x = Some τ ->
                     ρ x = Some v ->
                     dV_rel τ v
  }.

Arguments dG_rel _ _ : clear implicits.
Notation "'dGREL' ρ ∈ G[ Γ ]" :=
  (dG_rel Γ ρ)
    (at level 69, ρ at level 99, Γ at level 99).

Lemma extend_dgrel {Γ x ρ v τ} :
  (dGREL ρ ∈ G[Γ]) ->
  (dVREL v ∈ V[τ]) ->
  (dGREL ρ[x → v] ∈ G[Γ[x → τ]]).
Proof.
  split; try split; intro x';
unfold extend;
induction Var_eq_dec;
try (split; intro stupid; inversion stupid; fail);
try apply X;
try (eexists; trivial).

  intros.
  injection H.
  injection H0.
  intros.
  subst.
  auto.
Qed.

Definition related_expr (Γ : Env Ty) (e : Expr) (τ : Ty) : Type :=
  forall {ρ} (Hρ : dGREL ρ ∈ G[Γ]),
    (dEREL (ρ, e) ∈ E[τ]).

Lemma compat_real Γ r :
  related_expr Γ (e_pure (e_real r)) ℝ.
Proof.
  intros ρ Hρ σ.
  left.
  exists (v_real r, nnr_1).
  repeat econstructor.
  intros.
  inversion X; subst.
  f_equal.
  inversion H0.
  reflexivity.
Qed.

Lemma compat_var Γ x τ :
  Γ x = Some τ ->
  related_expr Γ (e_pure (e_var x)) τ.
Proof.
  intros Γτ.
  intros ρ Hρ σ.
  left.
  destruct (dG_rel_modeling Hρ).
  destruct (env_val_models x τ Γτ) as [v ρv].

  exists (v, nnr_1).
  repeat constructor; auto. {
    exact (dG_rel_V Hρ Γτ ρv).
  } {
    intros.
    inversion X; subst.
    f_equal.
    inversion H0.
    rewrite ρv in *.
    inversion H1.
    reflexivity.
  }
Qed.

Lemma compat_lam Γ x body τa τr :
  related_expr (Γ[x → τa]) body τr ->
  related_expr Γ (e_pure (e_lam x body)) (τa ~> τr).
Proof.
  intros Hbody.
  intros ρ Hρ σ.
  left.
  exists (v_clo x body ρ, nnr_1).
  constructor; [constructor |]. {
    intros va Hva.
    apply Hbody.
    apply extend_dgrel; auto.
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
  intros ρ Hρ σ.

  specialize (Hef ρ Hρ (π 0 σ)).
  specialize (Hea ρ Hρ (π 1 σ)).

  destruct Hef as [[[vf wf] [[Hvf EVAL_f] uf]] | not_ex]. {
    destruct Hea as [[[va wa] [[Hva EVAL_a] ua]] | not_ex]. {
      destruct vf; try contradiction.
      destruct (Hvf va Hva (π 2 σ)) as [[[vr wr] [[Hvr EVAL_r] ur]] | not_ex]. {
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
  intros ρ Hρ σ.

  specialize (He ρ Hρ σ).

  destruct He as [[[v w] [[Hv EVAL_e] u]] | not_ex]. {
    destruct v; try tauto.
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
  intros ρ Hρ σ.

  specialize (Hel ρ Hρ (π 0 σ)).
  specialize (Her ρ Hρ (π 1 σ)).

  destruct Hel as [[[vl wl] [[Hvl EVAL_l] ul]] | not_ex]. {
    destruct Her as [[[vr wr] [[Hvr EVAL_r] ur]] | not_ex]. {
      left.
      destruct vl, vr; try contradiction.
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

Lemma fundamental_property Γ e τ :
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

Theorem eval_dec :
  forall Γ ρ e τ σ,
    (TC Γ ⊢ e : τ) ->
    (ENV ρ ⊨ Γ) ->
    (existsT! vw : (Val * R+), let (v, w) := vw in EVAL ρ, σ ⊢ e ⇓ v, w) +
    ((existsT vw : (Val * R+), let (v, w) := vw in EVAL ρ, σ ⊢ e ⇓ v, w) -> False).
Proof.
  intros.
Qed.