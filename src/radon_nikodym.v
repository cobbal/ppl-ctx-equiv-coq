Require Import Basics.
Require Import Reals.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.fourier.Fourier.
Require Import nnr.
Require Import syntax.
Require Import utils.
Require Import Coq.Classes.Morphisms.
Require Import relations.
Require Import ctxequiv.
Require Import properties_of_relations.

Definition lebesgue_val_measure : Meas (val ℝ) :=
  pushforward lebesgue_measure v_real.

Goal forall e,
    is_RN_deriv (μ e) lebesgue_val_measure (fun v => obs_μ e v full_event).
  intros.
  hnf.
  extensionality A.
  unfold obs_μ.
  cbn.
  setoid_rewrite ennr_mul_1_l.
Abort.

Lemma change_of_variable : forall {X Y} (g : X -> Meas Y) (μ ν : Meas X) (dμdν : X -> R+),
    is_RN_deriv ν μ dμdν ->
    ν >>= g = μ >>= (fun x A => g x A * dμdν x).
Proof.
  intros.
  unfold is_RN_deriv in H.
  subst.
  rewrite meas_bind_assoc.
  extensionality A.
  integrand_extensionality x.
  setoid_rewrite ennr_mul_comm.
  rewrite integration_linear_in_meas.
  fold (dirac x).
  rewrite meas_id_left.
  trivial.
Qed.

Lemma scale_deriv r : is_RN_deriv
                       lebesgue_measure
                       (pushforward lebesgue_measure (Rmult r))
                       (const (ennr_abs r)).
Proof.
  simple refine (RN_deriv_is_coq_deriv _ _ _ _). {
    apply derivable_mult. {
      apply derivable_const.
    } {
      apply derivable_id.
    }
  } {
    intros.
    unfold const.
    unfold derive, derive_pt, const.
    destruct derivable_mult; cbn.
    unfold derivable_pt_abs in d.
    f_equal.
    unfold mult_fct in *.
    eapply uniqueness_limite; eauto.
    repeat intro.
    assert (0 < (2 * eps))%R by fourier.
    exists (mkposreal _ H0).
    intros.
    cbn in *.
    replace ((r * (x + h) - r * x) / h - r)%R with 0%R by (field; auto).
    unfold Rabs.
    destruct Rcase_abs; fourier.
  }
Qed.

Lemma lebesgue_scale r :
  lebesgue_measure = (fun A : Event R => (ennr_abs r) * pushforward lebesgue_measure (Rmult r) A).
Proof.
  setoid_rewrite <- meas_id_right at 1.
  erewrite change_of_variable; [| apply (scale_deriv r)].
  unfold pushforward, compose, preimage.
  extensionality A.
  unfold const.
  setoid_rewrite <- integration_linear_mult_r.
  unfold dirac.
  rewrite integration_of_indicator.
  ring.
Qed.

Lemma plus_deriv r : is_RN_deriv
                       lebesgue_measure
                       (pushforward lebesgue_measure (Rplus r))
                       (const 1).
Proof.
  simple refine (RN_deriv_is_coq_deriv _ _ _ _). {
    apply derivable_plus. {
      apply derivable_const.
    } {
      apply derivable_id.
    }
  } {
    intros.
    unfold const.
    unfold derive, derive_pt, const.
    destruct derivable_plus; cbn.
    unfold derivable_pt_abs in d.
    unfold plus_fct in *.
    enough (x0 = 1)%R. {
      subst.
      ennr.
      unfold Rabs.
      destruct Rcase_abs; auto; fourier.
    } {
      eapply uniqueness_limite; eauto.
      repeat intro.
      exists (mkposreal _ H).
      intros.
      cbn in *.
      replace ((r + (x + h) - (r + x)) / h - 1)%R with 0%R by (field; auto).
      unfold Rabs.
      destruct Rcase_abs; fourier.
    }
  }
Qed.

Lemma lebesgue_translate_invariant r :
  lebesgue_measure = pushforward lebesgue_measure (Rplus r).
Proof.
  setoid_rewrite <- meas_id_right at 1.
  erewrite change_of_variable; [| apply (plus_deriv r)].
  unfold const.
  setoid_rewrite ennr_mul_1_r.
  apply meas_id_right.
Qed.

Require Import logrel.
Import Log_rel1_prop.
Module RadonNikodymBase <: BASE.
  Definition V_rel_real : rel (val ℝ) := fun _ => True.

  Inductive E_rel'' : forall (τ : Ty) (ϕ : Effect) (v_rel_τ : rel (val τ)), rel (expr · τ ϕ) :=
  | E_rel'_obsR (v_rel_τ : rel (val ℝ)) e :
      is_RN_deriv (μ e) lebesgue_val_measure (fun v => obs_μ e v full_event) ->
      @E_rel'' ℝ ObsR v_rel_τ e
  | E_rel'_obsNone τ (v_rel_τ : rel (val τ)) e :
      @E_rel'' τ ObsNone v_rel_τ e.

  (* Coq can't handle inductive parameters, so add an extra bit of indirection *)
  Definition E_rel' τ ϕ (v_rel_τ : rel (val τ)) e :=
    (forall σ v w, (EVAL σ ⊢ e ⇓ v, w) -> v_rel_τ v) /\
    forall (Hτ : τ = ℝ)
           (Hϕ : ϕ = ObsR),
      let e' := (rew [fun ϕ => expr · ℝ ϕ] Hϕ in
                    rew [fun τ => expr · τ ϕ] Hτ in
                    e) in
      is_RN_deriv (μ e') lebesgue_val_measure (fun v => obs_μ e' v full_event).
End RadonNikodymBase.

Module RadonNikodymCases : CASES RadonNikodymBase.
  Module Defs := Defs RadonNikodymBase.
  Export Defs.

  Lemma case_val : forall τ v,
      V_rel τ v -> E_rel τ _ v.
  Proof.
    intros.
    split; [| discriminate]; intros.
    destruct (invert_eval_val H0); subst.
    auto.
  Qed.

  Lemma case_real : forall r,
      E_rel ℝ _ (e_real r).
  Proof.
    split; [| discriminate]; intros.
    constructor.
  Qed.

  Lemma case_lam : forall τa ϕ τr body,
      (forall v,
          V_rel τa v ->
          E_rel τr _ (proj1_sig (ty_subst1 body v))) ->
      E_rel (τa ~~ ϕ ~> τr) _ (e_lam body).
  Proof.
    split; [| discriminate]; intros.

    rewrite rewrite_v_lam in H0.
    destruct (invert_eval_val H0); subst.
    constructor; intros.
    apply H; auto.
  Qed.

  Lemma peer_inside_the_μ {τ ϕ X} (e : expr · τ ϕ) (f g : val τ -> Meas X) :
    E_rel _ _ e ->
    (forall v, V_rel τ v -> f v = g v) ->
    (μ e >>= f) = (μ e >>= g).
  Proof.
    intros.
    extensionality A.
    setoid_rewrite riemann_def_of_lebesgue_integration.
    integrand_extensionality t.
    integrand_extensionality σ.
    unfold eval_in, indicator.

    decide_eval as [v w ex u].
    cbn.
    destruct H as [H _].
    specialize (H _ _ _ ex).
    specialize (H0 _ H).
    rewrite H0.
    auto.
  Qed.

  Lemma case_app : forall τa ϕ τr ϕf ϕa ef ea,
      E_rel (τa ~~ ϕ ~> τr) ϕf ef ->
      E_rel τa ϕa ea ->
      E_rel τr _ (e_app ef ea).
  Proof.
    split; intros. {
      intros.
      d_destruct H1; try absurd_val.

      destruct H as [H _], H0 as [H0 _].
      specialize (H (π 0 σ) _ _ H1_).
      specialize (H0 (π 1 σ) _ _ H1_0).

      cbn in H.
      d_destruct H.
      specialize (H va H0).

      destruct H as [H _].
      eapply H; eauto.
    } {
      subst.
      subst e'.
      cbn.

      unfold is_RN_deriv.
      intros.
      rewrite by_μe_eq_μEntropy_app.
      rewrite obs_help_app.
      do 2 setoid_rewrite integration_linear_mult_l.
      unfold lebesgue_val_measure.
      rewrite bind_of_pushforward.
      unfold compose.

      change ((μ ef >>= (fun vf => μ ea >>= (fun va => μEntropy >>= apply_in vf va))) =
              lebesgue_measure >>=
               (fun x => μ ef >>=
                (fun vf => μ ea >>=
                 (fun va A =>
                    indicator A (v_real x) *
                    integration
                      (fun σ => obs_apply_in vf va (v_real x) σ full_event)
                      μEntropy)))).

      rewrite (tonelli lebesgue_measure); auto.
      apply peer_inside_the_μ; auto.
      intros vf Hvf.

      rewrite (tonelli lebesgue_measure); auto.
      apply peer_inside_the_μ; auto.
      intros va Hva.

      clear H H0 ef ea.

      destruct Hvf.
      specialize (H va Hva).
      rewrite elim_apply_in, elim_obs_apply_in.
      fold_μ.
      elim_sig_exprs.
      elim_erase_eqs.

      destruct H.
      specialize (H0 eq_refl eq_refl).
      cbn in H0.
      hnf in H0.

      extensionality A0.
      rewrite H0.

      unfold lebesgue_val_measure.
      rewrite bind_of_pushforward.
      auto.
    }
  Qed.

  Lemma case_factor : forall ϕ e,
      E_rel ℝ ϕ e ->
      E_rel ℝ _ (e_factor e).
  Proof.
    split; intros. {
      exact I.
    } {
      discriminate.
    }
  Qed.


  Lemma μ_sample :
    (* μ e_sample = μEntropy >>= (fun σ => dirac (v_real (proj1_sig (σ O)))). *)
    μ e_sample = pushforward μEntropy (fun σ => v_real (proj1_sig (σ O))).
  Proof.
    extensionality A.
    rewrite <- (meas_id_right (pushforward _ _)).
    rewrite bind_of_pushforward.
    unfold compose.
    integrand_extensionality σ.
    unfold eval_in.
    decide_eval as [v w ex u].
    cbn.
    d_destruct ex.
    unfold dirac.
    ring.
  Qed.

  Lemma meas_of_sample :
    μ e_sample = pushforward lebesgue_01_ivl v_real.
  Proof.
    extensionality A.
    rewrite μ_sample.
    rewrite <- (μEntropy_proj_is_lebesgue 0).
    auto.
  Qed.

  Lemma case_sample :
    E_rel ℝ _ e_sample.
  Proof.
    split; intros. {
      d_destruct H; try absurd_val.
      constructor.
    } {
      d_destruct (Hτ, Hϕ).
      subst e'.
      cbn.

      hnf.
      rewrite meas_of_sample.
      extensionality A.
      unfold pushforward, compose, lebesgue_01_ivl, lebesgue_val_measure.
      rewrite bind_of_pushforward.
      rewrite <- (meas_id_right lebesgue_measure) at 1.
      unfold ">>=".

      integrand_extensionality r.
      unfold dirac, compose, preimage, indicator.

      repeat destruct Rle_dec; destruct A; cbn; try ring; rewrite ennr_mul_1_l. {
        unfold obs_μ.
        cbn.
        erewrite int_const_entropy; auto.
        intros σ.
        ring_simplify.
        unfold obs.
        destruct determinism.obs_eval_dec. {
          inversion ev; auto.
        } {
          exfalso.
          eapply not_ex.
          constructor.
          auto.
        }
      } {
        unfold obs_μ.
        cbn.
        erewrite int_const_entropy; auto.
        intros σ.
        unfold obs.
        destruct determinism.obs_eval_dec; try ring.
        inversion ev.
        tauto.
      } {
        unfold obs_μ.
        cbn.
        erewrite int_const_entropy; auto.
        intro σ.
        unfold obs.
        destruct determinism.obs_eval_dec; try ring.
        inversion ev.
        tauto.
      }
    }
  Qed.

  Lemma case_observe : forall ϕ0 e0 e1,
      E_rel ℝ ϕ0 e0 ->
      E_rel ℝ _ e1 ->
      E_rel ℝ _ (e_observe e0 e1).
  Proof.
    split; intros. {
      exact I.
    } {
      discriminate.
    }
  Qed.

  Lemma case_hide : forall e,
      E_rel ℝ ObsR e ->
      E_rel ℝ ObsNone (e_hide_observable e).
  Proof.
    split; intros. {
      exact I.
    } {
      discriminate.
    }
  Qed.

  Definition score_meas {X} (w : X -> R+) (μ : Meas X) : Meas X :=
    μ >>= (fun x A => w x * indicator A x).


  Lemma case_binop : forall ϕl ϕr op el er,
      E_rel ℝ ϕl el ->
      E_rel ℝ ϕr er ->
      E_rel ℝ _ (e_binop op el er).
  Proof.
    split; intros. {
      exact I.
    } {
      subst ϕr e'.
      replace Hτ with (eq_refl ℝ) by apply (UIP_dec ty_eq_dec).
      clear Hτ.
      cbn.

      hnf; intros.
      rewrite by_μe_eq_μEntropy_op.
      rewrite obs_help_op.
      do 2 setoid_rewrite integration_linear_mult_l.
      unfold lebesgue_val_measure.
      rewrite bind_of_pushforward.
      unfold compose.

      change (μ el >>= (fun vl => μ er >>= op_in op vl) =
              lebesgue_measure >>=
               (fun x => μ el >>=
                 (fun vl A =>
                    integration
                      (fun σ =>
                         indicator A (v_real x) *
                         obs_op_in op vl er (v_real x) σ full_event)
                      μEntropy))).

      rewrite (tonelli lebesgue_measure); auto.
      apply peer_inside_the_μ; auto.
      intros vl _.
      destruct_val vl.

      clear H el.

      destruct op. {
        cbn.
        setoid_rewrite ennr_mul_1_l.
        unfold ennr_div.
        replace (/ _) with 1; revgoals. {
          cbn.
          destruct Req_EM_T. {
            unfold Rabs in e.
            destruct Rcase_abs; fourier.
          } {
            ennr.
            compute.
            destruct Rcase_abs; try fourier.
            rewrite Rinv_1.
            auto.
          }
        }

        setoid_rewrite ennr_mul_1_r.

        replace (μ er) with (lebesgue_val_measure
                               >>=
                               (fun x A => indicator A x * obs_μ er x full_event));
          revgoals.
        {
          symmetry.
          destruct H0 as [_ ?].
          apply (H eq_refl eq_refl).
        }
        unfold lebesgue_val_measure.
        rewrite bind_of_pushforward.
        rewrite meas_bind_assoc.
        unfold compose.

        unfold obs_μ.
        cbn.
        setoid_rewrite ennr_mul_1_l.

        setoid_rewrite ennr_mul_comm at 1.
        setoid_rewrite integration_linear_in_meas.

        transitivity (
            lebesgue_measure >>=
            (fun (x : R) (ev : Event (val ℝ)) =>
            integration (fun σ : Entropy => obs er (v_real x) σ) μEntropy *
            op_in Add (v_real r) (v_real x) ev)).
        {
          f_equal.
          extensionality x.
          extensionality A.
          fold (dirac (v_real x)).
          rewrite meas_id_left.
          auto.
        }
        cbn.

        rewrite (lebesgue_translate_invariant r) at 2.
        rewrite !bind_of_pushforward.
        unfold compose.
        extensionality A.
        integrand_extensionality x.
        rewrite <- integration_linear_mult_l.
        rewrite ennr_mul_comm.
        f_equal.
        integrand_extensionality σ.
        repeat f_equal.
        ring.
      } {
        cbn.
        setoid_rewrite ennr_mul_1_l.
        unfold ennr_div.

        replace (μ er) with (lebesgue_val_measure
                               >>=
                               (fun x A => indicator A x * obs_μ er x full_event));
          revgoals.
        {
          symmetry.
          destruct H0 as [_ ?].
          apply (H eq_refl eq_refl).
        }
        unfold lebesgue_val_measure.
        rewrite bind_of_pushforward.
        rewrite meas_bind_assoc.
        unfold compose.

        unfold obs_μ.
        cbn.
        destruct Req_EM_T. {
          exfalso.
          unfold Rabs in e.
          destruct Rcase_abs; fourier.
        }
        setoid_rewrite ennr_mul_1_l.

        setoid_rewrite ennr_mul_comm at 1.
        setoid_rewrite integration_linear_in_meas.

        transitivity (
            lebesgue_measure >>=
            (fun (x : R) (ev : Event (val ℝ)) =>
            integration (fun σ : Entropy => obs er (v_real x) σ) μEntropy *
            op_in ConstDouble (v_real r) (v_real x) ev)).
        {
          f_equal.
          extensionality x.
          extensionality A.
          fold (dirac (v_real x)).
          rewrite meas_id_left.
          auto.
        }
        cbn.

        rewrite (lebesgue_scale 2) at 2.
        setoid_rewrite integration_linear_in_meas.
        rewrite !bind_of_pushforward.
        unfold compose.
        extensionality A.
        setoid_rewrite integration_linear_mult_l.
        integrand_extensionality x.
        setoid_rewrite ennr_mul_comm at 2.
        rewrite <- integration_linear_mult_l.
        rewrite <- ennr_mul_assoc.
        replace (ennr_abs 2) with 2; revgoals. {
          ennr.
          unfold Rabs.
          destruct Rcase_abs; auto; fourier.
        }
        rewrite (integration_linear_mult_r _ 2).
        rewrite ennr_mul_comm.
        f_equal.
        integrand_extensionality σ.

        replace (2 * x / 2)%R with x by field.
        rewrite <- ennr_mul_assoc.
        replace (_ * 2) with 1; try ring.
        ennr.
        unfold Rabs.
        destruct Rcase_abs; try fourier.
        field.
      }
    }
  Qed.
End RadonNikodymCases.

Module RadonNikodymCompat := Compatibility RadonNikodymBase RadonNikodymCases.
Import RadonNikodymCases RadonNikodymCompat.

Lemma radon_nikodym (e : expr · ℝ ObsR) :
  is_RN_deriv (μ e) lebesgue_val_measure (fun v => obs_μ e v full_event).
Proof.
  pose proof fundamental_property e dep_nil I as fp.
  replace (proj1_sig _) with e in fp; revgoals. {
    elim_sig_exprs.
    elim_erase_eqs.
    auto.
  }
  destruct fp.
  specialize (H0 eq_refl eq_refl).
  cbn in *.
  exact H0.
Qed.

Print Assumptions radon_nikodym.
