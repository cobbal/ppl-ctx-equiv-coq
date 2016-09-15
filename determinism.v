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

Definition dE_rel' (τ : Ty) (dV_rel_τ : Val -> Type) (e : Expr) : Type :=
  forall σ,
    (existsT (vw : Val * R+),
     let (v, w) := vw in
     (dV_rel_τ v)
       ⨉ (EVAL σ ⊢ e ⇓ v, w)
       ⨉ (forall v' w', (EVAL σ ⊢ e ⇓ v', w') -> (v, w) = (v', w'))
    ) +
    ((existsT vw : (Val * R+), let (v, w) := vw in EVAL σ ⊢ e ⇓ v, w) -> False).

Definition dV_rel_real (v : Val) : Type :=
  match v : Expr with
  | e_real _ => True
  | _ => False
  end.

Definition dV_rel_arrow
       (τa τr : Ty) (dV_rel_a dV_rel_r : Val -> Type)
       (v : Val)
  : Type
  := match v : Expr with
     | e_lam τa' body =>
       (τa = τa') ⨉
       { tc_body : (TC (extend · τa) ⊢ body : τr) &
         forall {va : WT_Val τa} (Hva : dV_rel_a va),
          (dE_rel' τr dV_rel_r (body.[va : Expr/]))
       }
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

Definition dG_rel {Γ} {ρ : WT_Env Γ} : Type :=
  forall {x v τ},
    lookup Γ x = Some τ ->
    lookup ρ x = Some v ->
    dV_rel τ v.
Arguments dG_rel _ _ : clear implicits.

(* Notation "'dGREL' ρ ∈ G[ Γ ]" := *)
(*   (dG_rel Γ ρ) *)
(*     (at level 69, ρ at level 99, Γ at level 99). *)

Lemma tc_of_dV_rel {τ v} :
  dV_rel τ v ->
  (TC · ⊢ v : τ).
Proof.
  intros.
  destruct τ, v as [[]]; simpl in *; try tauto. {
    constructor.
  } {
    destruct X.
  } {
    destruct X.
  } {
    destruct X.
    destruct s.
    subst.
    econstructor; eauto.
  }
Qed.

Lemma extend_dgrel {Γ ρ τ} {v : WT_Val τ} :
  (dG_rel Γ ρ) ->
  (dV_rel τ v) ->
  (dG_rel (extend Γ τ) (extend_WT_Env ρ v)).
Proof.
  intros.
  intros x ? ? Γx ρx.
  destruct x; intros. {
    simpl in *.
    inversion Γx.
    inversion ρx.
    subst.
    auto.
  } {
    apply (X x); auto.
  }
Qed.


Definition related_expr (Γ : Env Ty) (e : Expr) (τ : Ty) : Type :=
  (TC Γ ⊢ e : τ)
    ⨉ (forall {ρ} (Hρ : dG_rel Γ ρ),
          (dE_rel τ (e.[subst_of_WT_Env ρ]))).

Lemma compat_real Γ r :
  related_expr Γ (e_real r) ℝ.
Proof.
  split; [exact (TCReal _) |].
  intros ρ Hρ σ.
  left.
  exists (mk_Val (e_real r) I, nnr_1).
  repeat constructor. {
    apply EPure'.
    reflexivity.
  } {
    intros.
    inversion X; subst.
    f_equal.
    apply Val_eq.
    auto.
  }
Qed.

Lemma compat_var Γ x τ :
  lookup Γ x = Some τ ->
  related_expr Γ (e_var x) τ.
Proof.
  intros Γτ.
  split; [exact (TCVar Γτ) |].
  intros ρ Hρ σ.
  left.

  destruct (env_search (WT_Env_tc ρ) Γτ) as [v ρv].
  exists (v : Val, nnr_1).
  repeat constructor; auto. {
    eapply Hρ; eauto.
  } {
    simpl.
    pose proof subst_of_WT_Env_lookup ρv.
    rewrite H.
    apply EPure.
  } {
    intros.
    simpl in X.
    rewrite (subst_of_WT_Env_lookup ρv) in X.
    destruct v as [[]].
    simpl in *.
    destruct Val_e; try tauto. {
      inversion X; subst.
      f_equal.
      apply Val_eq.
      auto.
    } {
      inversion X; subst.
      f_equal.
      apply Val_eq.
      auto.
    }
  }
Qed.

Lemma compat_lam Γ body τa τr :
  related_expr (extend Γ τa) body τr ->
  related_expr Γ (e_lam τa body) (τa ~> τr).
Proof.
  intros Hbody.
  destruct Hbody as [tc_body Hbody].
  split; [exact (TCLam tc_body) |].
  intros ρ Hρ σ.
  left.

  pose (mk_Val (e_lam τa body.[up (subst_of_WT_Env ρ)]) I).

  eexists (v, nnr_1).
  constructor; [constructor |]. {
    simpl.
    split; auto.
    exists (body_subst ρ tc_body).
    intros.
    rewrite subst_comp.
    replace (up (subst_of_WT_Env ρ) >> (va : Expr) .: ids)
    with (subst_of_WT_Env (extend_WT_Env ρ va))
      by autosubst.
    apply (Hbody _ (extend_dgrel Hρ Hva)).
  } {
    apply EPure'.
    auto.
  } {
    intros.
    inversion X; subst.
    f_equal.
    apply Val_eq.
    simpl.
    auto.
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
  split; [exact (TCApp tc_ef tc_ea) |].
  intros ρ Hρ σ.

  specialize (Hef ρ Hρ (π 0 σ)).
  specialize (Hea ρ Hρ (π 1 σ)).

  destruct Hef as [[[vf wf] [[Hvf EVAL_f] uf]] | not_ex]. {
    destruct Hea as [[[va wa] [[Hva EVAL_a] ua]] | not_ex]. {
      destruct vf using Val_rect; try contradiction.
      destruct Hvf as [? [tc_body Hvf]].
      subst τa0.
      pose (wt_va := mk_WT_Val _ (tc_of_dV_rel Hva)).
      destruct (Hvf wt_va Hva (π 2 σ)) as [[[vr wr] [[Hvr EVAL_r] ur]] | not_ex]. {
        left.
        exists (vr, wf [*] wa [*] wr).
        repeat econstructor; eauto.
        intros.
        simpl in X.
        inversion X; subst; try absurd_Val.

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
        inversion y; subst; try absurd_Val.

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
      inversion y; subst; try absurd_Val.

      eexists (_, _); eauto.
    }
  } {
    right.
    intros.
    apply not_ex.
    destruct X as [[? ?] ?].
    inversion y; subst; try absurd_Val.

    eexists (_, _); eauto.
  }
Qed.

Lemma compat_factor Γ e :
  related_expr Γ e ℝ ->
  related_expr Γ (e_factor e) ℝ.
Proof.
  intros He.
  destruct He as [tc_e He].
  split; [exact (TCFactor tc_e) |].
  intros ρ Hρ σ.

  specialize (He ρ Hρ σ).

  destruct He as [[[v w] [[Hv EVAL_e] u]] | not_ex]. {
    destruct v using Val_rect; try contradiction.
    destruct (Rle_dec 0 r). {
      left.
      exists (mk_Val (e_real r) I, mknnr r r0 [*] w).
      repeat constructor; eauto.
      intros.
      inversion X.
      absurd_Val.
      subst.

      specialize (u _ _ X0).
      inversion u; subst.
      do 2 f_equal.
      nnr; simpl; auto.
    } {
      right.
      intros.

      destruct X as [[? ?] ?].
      inversion y; subst; try absurd_Val.

      specialize (u _ _ X).
      inversion u; subst.

      tauto.
    }
  } {
    right.
    intros.
    apply not_ex.

    destruct X as [[? ?] ?].
    inversion y; subst; try absurd_Val.
    eexists (_, _).
    exact X.
  }
Qed.

Lemma compat_sample Γ :
  related_expr Γ e_sample ℝ.
Proof.
  split; [exact TCSample |].
  left.
  eexists (mk_Val (e_real (proj1_sig (σ O))) I, nnr_1).
  split. {
    split; hnf; auto.
    apply ESample.
  }

  intros.
  inversion X; try absurd_Val.
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
  split; [exact (TCPlus tc_el tc_er) |].
  intros ρ Hρ σ.

  specialize (Hel ρ Hρ (π 0 σ)).
  specialize (Her ρ Hρ (π 1 σ)).

  destruct Hel as [[[vl wl] [[Hvl EVAL_l] ul]] | not_ex]. {
    destruct Her as [[[vr wr] [[Hvr EVAL_r] ur]] | not_ex]. {
      left.
      destruct vl using Val_rect;
destruct vr using Val_rect;
try (destruct Hvl, Hvr; contradiction).
      exists (mk_Val (e_real (r + r0)) I, wl [*] wr).
      repeat econstructor; eauto; auto.

      intros.
      inversion X; subst; try absurd_Val.

      specialize (ul _ _ X0).
      specialize (ur _ _ X1).
      inversion ul.
      inversion ur.
      auto.
    } {
      right.
      intros.
      destruct X as [[? ?] ?].
      inversion y; subst; try absurd_Val.

      contradict not_ex.
      eexists (_, _); eauto.
    }
  } {
    right.
    intros.
    destruct X as [[? ?] ?].
    inversion y; subst; try absurd_Val.

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

(* Lemma fundamental_environment {Γ ρ} : *)
(*   (TCEnv ⊢ ρ : Γ) -> *)
(*   (dG_rel Γ ρ). *)
(* Proof. *)
(*   intros Hρ. *)

(*   induction Hρ using tc_env_val_rect *)
(*   with (P := fun v τ Hv => dV_rel τ v). { *)
(*     intros. *)
(*     repeat constructor. *)
(*   } { *)
(*     intros. *)
(*     split; auto. *)
(*     exists Γ_clo. *)
(*     exists Hρ. *)
(*     exists t. *)
(*     intros. *)
(*     pose proof fundamental_property t. *)
(*     destruct X. *)
(*     refine (d _ _). *)
(*     apply extend_dgrel; auto. *)
(*   } { *)
(*     repeat constructor. *)
(*     intros. *)
(*     destruct x; discriminate H. *)
(*   } { *)
(*     intros. *)
(*     repeat constructor; auto. *)
(*     intros. *)

(*     destruct x; simpl in *. { *)
(*       inversion H. *)
(*       inversion H0. *)
(*       subst. *)
(*       auto. *)
(*     } { *)
(*       eapply IHHρ; eauto. *)
(*     } *)
(*   } *)
(* Qed. *)

Lemma dG_nil : dG_rel · (mk_WT_Env TCENil).
Proof.
  repeat intro.
  discriminate H.
Qed.

Theorem eval_dec {e τ} :
  (TC · ⊢ e : τ) ->
  forall σ,
    (existsT! vw : (Val * R+), let (v, w) := vw in EVAL σ ⊢ e ⇓ v, w) +
    ((existsT vw : (Val * R+), let (v, w) := vw in EVAL σ ⊢ e ⇓ v, w) -> False).
Proof.
  intros He σ.
  destruct (fundamental_property He).

  specialize (d _ dG_nil σ).
  replace e.[subst_of_WT_Env _] with e in * by autosubst.
  destruct d; [|right; auto]. {
    left.
    destruct s as [[v w] [[? ?] ?]].
    exists (v, w).
    split; auto.
    intro.
    destruct x'.
    apply e1.
  }
Qed.

Theorem big_preservation :
  forall {e τ v w σ},
    (TC · ⊢ e : τ) ->
    (EVAL σ ⊢ e ⇓ v, w) ->
    (TC · ⊢ v : τ).
Proof.
  intros.
  destruct (fundamental_property X).
  specialize (d _ dG_nil σ).
  replace e.[subst_of_WT_Env _] with e in * by autosubst.
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
