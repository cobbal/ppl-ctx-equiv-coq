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
  (dG_rel Γ ρ) ->
  forall x τ v,
    lookup Γ x = Some τ ->
    dep_lookup ρ x = Some (existT _ τ v) ->
    dV_rel τ v.
Proof.
  intros.
  simpl in *.
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

Lemma lookup_subst {Γ x τ v} (ρ : wt_env Γ) :
  dep_lookup ρ x = Some (existT val τ v) ->
  erase_wt_env ρ x = erase v.
Proof.
  revert Γ ρ.
  induction x; intros. {
    destruct ρ; inversion H; subst.
    dependent destruction H2.
    auto.
  } {
    destruct ρ; inversion H; subst.
    simpl.
    apply IHx.
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
    apply erase_injective.
    rewrite e.
    apply lookup_subst.
    auto.
  } {
    intros.
    destruct close; simpl in *.
    rewrite (lookup_subst ρ ρv) in e.
    apply erase_injective in e.
    subst.

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
    replace (proj1_sig _) with x in Hbody; auto.

    apply erase_injective.
    rewrite e; clear e.

    destruct close, body_subst; simpl in *.
    rewrite e0, e.
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

    dependent destruction x; inversion e.
    rewrite <- e0 in H2.
    apply erase_injective in H2.
    subst.
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

  destruct Hef as [[[vf wf] [[Hvf EVAL_f] uf]] | not_ex]. {
    destruct Hea as [[[va wa] [[Hva EVAL_a] ua]] | not_ex]. {
      destruct_val vf.
      destruct Hvf as [body0 Hvf].
      clear body.

      destruct (Hvf va Hva (π 2 σ)) as [[[vr wr] [[Hvr EVAL_r] ur]] | not_ex]. {
        left.
        exists (vr, wf [*] wa [*] wr).

        repeat destruct close; simpl in *.
        rewrite <- e, <- e0 in e1.
        destruct x1; inversion e1.
        assert (τa0 = τa). {
          pose proof expr_type_unique _ _ H0.
          inversion H.
          auto.
        }
        subst.
        apply erase_injective in H0.
        apply erase_injective in H1.
        subst.

        repeat econstructor; eauto.

        intros.
        dependent destruction H; subst. {
          exfalso.
          destruct v.
          simpl in *.
          subst.
          contradiction H.
        }

        specialize (uf _ _ H).
        specialize (ua _ _ H0).
        dependent destruction uf.
        dependent destruction ua.

        specialize (ur _ _ H1).
        dependent destruction ur.

        reflexivity.
      } {
        right.
        intros.
        apply not_ex.
        destruct X as [[? ?] ?].

        repeat destruct close; simpl in *.
        rewrite <- e, <- e0 in e1.
        destruct x1; inversion e1.
        assert (τa0 = τa). {
          pose proof expr_type_unique _ _ H0.
          inversion H.
          auto.
        }
        subst.
        apply erase_injective in H0.
        apply erase_injective in H1.
        subst.

        dependent destruction y. {
        }

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
