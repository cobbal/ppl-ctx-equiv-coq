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

Lemma change_of_variable : forall {X Y} (g : X -> Meas Y) (μ ν : Meas X) (dμdν : X -> R+),
    is_RN_deriv ν μ dμdν ->
    ν >>= g = μ >>= (fun x A => g x A * dμdν x).
Proof.
  intros.
  unfold is_RN_deriv in H.
  subst.
  rewrite meas_bind_assoc.
  integrand_extensionality x.
  setoid_rewrite ennr_mul_comm.
  rewrite integration_linear_in_meas.
  fold (dirac x).
  rewrite meas_id_left.
  trivial.
Qed.

Lemma δ1_bijection op : partial_bijection (δ1 op) (δ1_inv op).
Proof.
  split; [apply δ1_inv_complete | apply δ1_inv_sound].
Qed.

Lemma δ1_deriv op :
    is_RN_deriv
      (meas_option (pushforward lebesgue_measure (δ1 op)))
      lebesgue_measure
      (option0 ∘
         (fun x => ennr_inv <$> (ennr_abs <$> (δ1_partial_deriv op <$> δ1_inv op x)))).
Proof.
  refine (RN_deriv_is_coq_deriv_partial
            _
            (δ1_inv op)
            _
            (δ1_partially_derivable _)
            (δ1_bijection _)
            _).

  intros.

  remember (δ1_inv _ _).
  destruct o; cbn; auto.

  unfold partially_derive.
  set (δ1_partially_derivable _ _ _).
  clearbody d.
  apply eq_sym, δ1_inv_sound in Heqo.
  remember (δ1 op r).
  destruct o; inject Heqo.
  destruct d.
  cbn.
  repeat f_equal.

  eapply uniqueness_limite; eauto.
  apply δ1_partial_deriv_correct.
  rewrite <- Heqo0.
  discriminate.
Qed.


Lemma δ2_bijection op v0 :
  binop_effect op = ObsR ->
  partial_bijection (δ2 op v0) (δ2_inv op v0).
Proof.
  split; [apply δ2_inv_complete | apply δ2_inv_sound]; auto.
Qed.

Lemma δ2_deriv op v0 :
  binop_effect op = ObsR ->
  is_RN_deriv
    (meas_option (pushforward lebesgue_measure (δ2 op v0)))
    lebesgue_measure
    (option0 ∘
             (fun x => ennr_inv <$> (ennr_abs <$> (δ2_partial_deriv op v0 <$> δ2_inv op v0 x)))).
Proof.
  intros.
  refine (RN_deriv_is_coq_deriv_partial
            _
            (δ2_inv op v0)
            _
            (δ2_partially_derivable _ _)
            (δ2_bijection _ _ H)
            _).
  intros.
  remember (δ2_inv _ _ _).
  destruct o; cbn; auto.

  unfold partially_derive.
  set (δ2_partially_derivable _ _ _ _).
  clearbody d.
  apply eq_sym, δ2_inv_sound in Heqo.
  remember (δ2 op v0 r).
  destruct o; inject Heqo.
  destruct d.
  cbn.
  repeat f_equal.

  eapply uniqueness_limite; eauto.
  apply δ2_partial_deriv_correct.
  rewrite <- Heqo0.
  discriminate.
Qed.

Lemma lebesgue_δ1_invariant op :
  score_meas
    (fun x =>
       option0 (ennr_inv <$> (ennr_abs <$> (δ1_partial_deriv op <$> (δ1_inv op x)))))
    lebesgue_measure =
  meas_option (pushforward lebesgue_measure (δ1 op)).
Proof.
  setoid_rewrite <- meas_id_right at 3.
  erewrite change_of_variable; revgoals. {
    apply δ1_deriv.
  } {
    unfold compose.
    integrand_extensionality x.
    unfold dirac.
    ring.
  }
Qed.

Lemma lebesgue_δ2_invariant op v0 :
  binop_effect op = ObsR ->
  score_meas
    (fun x =>
       option0 (ennr_inv <$> (ennr_abs <$> (δ2_partial_deriv op v0 <$> δ2_inv op v0 x))))
    lebesgue_measure =
  meas_option (pushforward lebesgue_measure (δ2 op v0)).
Proof.
  intros.
  setoid_rewrite <- (meas_id_right (meas_option (pushforward lebesgue_measure (δ2 op v0)))).
  erewrite change_of_variable; revgoals. {
    apply δ2_deriv; auto.
  } {
    unfold compose.
    integrand_extensionality x.
    unfold dirac.
    ring.
  }
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

  Lemma case_binop : forall ϕl ϕr ϕ op Hϕ el er,
      E_rel ℝ ϕl el ->
      E_rel ℝ ϕr er ->
      E_rel ℝ ϕ (e_binop op Hϕ el er).
  Proof.
    split; intros. {
      exact I.
    } {
      move Hϕ0 after Hϕ.
      subst ϕ.
      d_destruct Hτ.
      cbn in e'.
      subst e'.

      assert (ϕr = ObsR) by (destruct ϕr, op; auto); subst.
      assert (binop_effect op = ObsR) by (destruct op; auto); subst.

      hnf; intros.
      rewrite by_μe_eq_μEntropy_binop.
      rewrite obs_help_binop.
      do 2 setoid_rewrite integration_linear_mult_l.
      unfold lebesgue_val_measure.
      rewrite bind_of_pushforward.
      unfold compose.

      change (μ el >>= (fun vl => μ er >>= binop_in op vl) =
              lebesgue_measure >>=
               (fun x => μ el >>=
                 (fun vl A =>
                    integration
                      (fun σ =>
                         indicator A (v_real x) *
                         obs_binop_in op vl er (v_real x) σ full_event)
                      μEntropy))).

      rewrite (tonelli lebesgue_measure); auto.
      apply peer_inside_the_μ; auto.
      intros vl _.
      destruct_val vl.

      clear H el.

      replace (μ er)
      with (lebesgue_val_measure
              >>= (fun x A => indicator A x * obs_μ er x full_event));
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
          score_meas
            (fun x => integration (obs er (v_real x)) μEntropy)
            lebesgue_measure >>=
                           (fun (x : R) => binop_in op (v_real r) (v_real x))).
                           (* (fun (x : R) (ev : Event (val ℝ)) => *)
                           (*    integration (fun σ : Entropy => obs er (v_real x) σ) μEntropy * *)
                           (*    op_in op (v_real r) (v_real x) ev)). *)
      {
        rewrite bind_of_score.
        integrand_extensionality x.
        fold (dirac (v_real x)).
        rewrite meas_id_left.
        reflexivity.
      }
      cbn.

      setoid_rewrite weird_δ2_correct.
      remember (weird_δ2 _ _).
      destruct o; cbn; revgoals. {
        destruct op; try contradiction; try discriminate.
        cbn in *.
        destruct Req_EM_T; try discriminate; subst.
        transitivity (empty_meas (val ℝ)). {
          extensionality A.
          apply integration_of_0.
        } {
          extensionality A.
          cbn.
          unfold ">>=".
          replace 0 with (integration (fun _ => 0) lebesgue_measure)
            by apply integration_of_0.
          integrand_extensionality x.

          rewrite δ2_inv_checked_fail.
          unfold const.
          rewrite <- integration_linear_mult_r.
          cbn.
            ring.
        }
      } {
        replace (fun x => dirac (v_real (r0 x))) with (dirac ∘ (v_real ∘ r0))
          by reflexivity.
        rewrite <- pushforward_as_bind.
        rewrite pushforward_compose.

        rewrite <- meas_id_right at 1.
        rewrite bind_of_pushforward.

        setoid_rewrite <- integration_linear_mult_l.

        transitivity
          (lebesgue_measure
             >>=
             fun (x0 : R) (A : Event (val ℝ)) =>
               indicator A (v_real x0) *
               match δ2_inv op r x0 with
               | Some ri => integration (obs er (v_real ri)) μEntropy
                                        / ennr_abs (δ2_partial_deriv op r ri)
               | None => 0
               end);
          revgoals.
        {
          integrand_extensionality x.
          f_equal.
          destruct δ2_inv. {
            setoid_rewrite integration_linear_mult_r.
            integrand_extensionality σ.
            cbn.
            unfold ennr_div.
            ring.
          } {
            apply eq_sym, integration_of_0.
          }
        }

        rewrite push_score' with (g_inv := δ2_inv op r); revgoals. {
          intros.
          pose proof weird_δ2_correct op r x.
          rewrite <- Heqo in H.
          cbn in H.
          remember (r0 x).
          clear Heqo r0 Heqr1.

          erewrite δ2_inv_complete; eauto.
          reflexivity.
        }

        rewrite bind_of_score.
        unfold compose.

        replace (pushforward lebesgue_measure r0)
        with (meas_option (pushforward lebesgue_measure (δ2 op r))); revgoals. {
          pose proof weird_δ2_correct op r.
          rewrite <- Heqo in H.
          cbn in H.
          replace (δ2 op r) with (Some ∘ r0); revgoals. {
            extensionality x.
            rewrite H.
            reflexivity.
          }
          rewrite <- meas_id_right at 1.
          rewrite bind_meas_option.
          rewrite pushforward_compose.
          rewrite pushforward_as_bind.
          rewrite meas_bind_assoc.
          rewrite <- meas_id_right.
          integrand_extensionality x.
          unfold compose.
          rewrite meas_id_left.
          reflexivity.
        }

        rewrite <- lebesgue_δ2_invariant; auto.

        unfold score_meas.
        rewrite meas_bind_assoc.
        integrand_extensionality x.
        rewrite integration_linear_in_meas.
        fold (dirac x).
        rewrite meas_id_left.
        destruct δ2_inv; cbn; try ring.

        unfold dirac, ennr_div.
        ring.
      }
    }
  Qed.

  Lemma case_unop : forall ϕ op e,
      E_rel ℝ ϕ e ->
      E_rel ℝ ϕ (e_unop op e).
  Proof.
    split; intros. {
      exact I.
    } {
      d_destruct Hτ.
      subst e' ϕ.
      cbn.

      hnf.
      rewrite by_μe_eq_μEntropy_unop.
      rewrite obs_help_unop.
      setoid_rewrite integration_linear_mult_l.
      unfold lebesgue_val_measure.
      rewrite bind_of_pushforward.
      unfold compose.

      replace (μ e)
      with (lebesgue_val_measure
              >>= (fun x A => indicator A x * obs_μ e x full_event));
        revgoals.
      {
        destruct H as [_ ?].
        apply (eq_sym (H eq_refl eq_refl)).
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
          score_meas
            (fun x => integration (obs e (v_real x)) μEntropy)
            lebesgue_measure >>=
                           (fun (x : R) => unop_in op (v_real x))).
      {
        rewrite bind_of_score.
        integrand_extensionality x.
        rewrite (meas_id_left (v_real x)).
        reflexivity.
      }

      transitivity
      (lebesgue_measure
         >>=
         fun (x0 : R) (A : Event (val ℝ)) =>
           indicator A (v_real x0) *
           match δ1_inv op x0 with
           | Some ri => integration (obs e (v_real ri)) μEntropy
                                    / ennr_abs (δ1_partial_deriv op ri)
           | None => 0
           end);
        revgoals.
      {
        integrand_extensionality x.
        rewrite <- integration_linear_mult_l.
        f_equal.
        destruct δ1_inv; revgoals. {
          rewrite integration_of_0.
          reflexivity.
        } {
          setoid_rewrite ennr_mul_1_l.
          unfold ennr_div.
          rewrite integration_linear_mult_r.
          reflexivity.
        }
      }
      transitivity
      (meas_option
         (pushforward
            (score_meas (fun x => integration (obs e (v_real x)) μEntropy) lebesgue_measure)
            (δ1 op)) >>= (dirac ∘ v_real)).
      {
        rewrite bind_meas_option.
        rewrite pushforward_as_bind.
        set (score_meas _ _).
        clearbody m.
        rewrite meas_bind_assoc.
        integrand_extensionality x.
        unfold compose.
        rewrite meas_id_left.
        cbn.
        destruct δ1; reflexivity.
      }

      transitivity
      (meas_option
         (pushforward
            (score_meas (fun x =>
                           match δ1 op x with
                           | Some _ => 1
                           | None => 0
                           end *
                           integration (obs e (v_real x)) μEntropy) lebesgue_measure)
            (δ1 op)) >>= (dirac ∘ v_real)).
      {
        rewrite 2 bind_meas_option.
        rewrite 2 bind_of_pushforward.
        unfold flip, compose.
        unfold score_meas.
        rewrite 2 meas_bind_assoc.
        integrand_extensionality x.
        rewrite 2 integration_linear_in_meas.
        rewrite (meas_id_left x).
        destruct δ1; cbn; ring.
      }

      rewrite (push_score _ _ _ _ (δ1_bijection op)); revgoals. {
        intros.
        rewrite H0.
        ring.
      }

      rewrite bind_meas_option.
      rewrite bind_of_score.

      transitivity (
          meas_option (pushforward lebesgue_measure (δ1 op))
                      >>=
                      (fun a ev =>
                         option0
                           ((fun x =>
                               integration (obs e (v_real x)) μEntropy)
                              <$> (δ1_inv op a)) *
                         (dirac (v_real a) ev))).
      {
        rewrite bind_meas_option.
        rewrite 2 bind_of_pushforward.
        integrand_extensionality r.
        unfold flip, compose.
        remember (δ1 _ _).
        destruct o; cbn; try ring.
        erewrite δ1_inv_complete; eauto.
        cbn.
        rewrite <- Heqo.
        ring.
      }

      rewrite <- lebesgue_δ1_invariant.

      unfold score_meas.
      rewrite meas_bind_assoc.
      integrand_extensionality x.
      rewrite integration_linear_in_meas.
      fold (dirac x).
      rewrite meas_id_left.
      destruct δ1_inv; cbn; try ring.

      unfold dirac, ennr_div.
      ring.
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
