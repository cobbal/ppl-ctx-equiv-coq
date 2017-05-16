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

Lemma δ1_bijection op : partial_bijection (δ1_dom op) (δ1' op) (δ1'_inv op).
Proof.
  repeat intro.
  cbn in *.
  remember (δ1 _ _) in *.
  destruct o; cbn; try discriminate.
  erewrite δ1_inv_complete; eauto.
  reflexivity.
Qed.

Lemma δ1_deriv op :
    is_RN_deriv
      (pushforward (restrict_meas lebesgue_measure (δ1_dom op)) (δ1' op))
      lebesgue_measure
      (δ1'_partial_deriv_inv op).
Proof.
  refine (RN_deriv_is_coq_deriv_partial
            (δ1_dom op)
            (δ1' op)
            (δ1'_inv op)
            _
            (δ1_partially_derivable _)
            (δ1_bijection _)
            _).
  split; intros. {
    unfold δ1'_partial_deriv_inv, partially_derive.
    destruct H as [? [? ?]].
    cbn in *.

    remember (δ1 _ _).
    destruct o; cbn in *; try discriminate.
    subst.

    erewrite δ1_inv_complete; eauto.
    cbn.
    do 2 f_equal.

    (* Dependent types can get really ugly sometimes... *)
    set (δ1_partially_derivable _ _).
    cbn in *.
    set (δ1 _ _) in *.
    clearbody d.
    pose proof (Heqo : Some y = δ1 op x) as Heqo'.
    clearbody o.
    subst o.
    destruct d; cbn.

    eapply uniqueness_limite; eauto.
    apply δ1_partial_deriv_correct.
    cbn.
    rewrite <- Heqo'.
    reflexivity.
  } {
    unfold δ1'_partial_deriv_inv.
    cbn.
    remember (δ1_inv _ _).
    destruct o; auto.
    contradict H.
    exists r.
    cbn.
    erewrite δ1_inv_sound; cbn; eauto.
  }
Qed.

Lemma δ2_bijection op v0 :
  binop_effect op = ObsR ->
  partial_bijection (δ2_dom op v0) (δ2' op v0) (δ2'_inv op v0).
Proof.
  repeat intro.
  cbn in *.
  remember (δ2 _ _ _) in *.
  destruct o; cbn; try discriminate.
  pose proof (δ2_inv_complete H (eq_sym Heqo)).
  unfold δ2'_inv.
  rewrite H1.
  reflexivity.
Qed.

Lemma δ2_deriv op v0 :
  binop_effect op = ObsR ->
  is_RN_deriv
    (pushforward (restrict_meas lebesgue_measure (δ2_dom op v0)) (δ2' op v0))
    lebesgue_measure
    (δ2'_partial_deriv_inv op v0).
Proof.
  intros.
  refine (RN_deriv_is_coq_deriv_partial
            (δ2_dom op v0)
            (δ2' op v0)
            (δ2'_inv op v0)
            _
            (δ2_partially_derivable _ _)
            (δ2_bijection _ _ H)
            _).
  split; intros. {
    unfold δ2'_partial_deriv_inv, partially_derive.
    destruct H0 as [? [? ?]].
    cbn in *.

    remember (δ2 _ _ _).
    destruct o; cbn in *; try discriminate.
    subst.

    erewrite δ2_inv_complete; eauto.
    cbn.
    do 2 f_equal.

    set (δ2_partially_derivable _ _ _).
    cbn in *.
    set (δ2 _ _ _) in *.
    clearbody d.
    pose proof (Heqo : Some y = δ2 op v0 x) as Heqo'.
    clearbody o.
    subst o.
    destruct d; cbn.

    eapply uniqueness_limite; eauto.
    apply δ2_partial_deriv_correct.
    cbn.
    rewrite <- Heqo'.
    reflexivity.
  } {
    unfold δ2'_partial_deriv_inv.
    cbn.
    remember (δ2_inv _ _ _).
    destruct o; auto.
    contradict H0.
    exists r.
    cbn.
    erewrite δ2_inv_sound; cbn; eauto.
  }
Qed.

Lemma lebesgue_δ1_invariant op :
  score_meas (δ1'_partial_deriv_inv op) lebesgue_measure =
  pushforward (restrict_meas lebesgue_measure (δ1_dom op)) (δ1' op).
Proof.
  setoid_rewrite <- meas_id_right at 3.
  erewrite change_of_variable; revgoals. {
    apply δ1_deriv.
  } {
    integrand_extensionality v.
    unfold dirac.
    ring.
  }
Qed.

Lemma lebesgue_δ2_invariant op v0 :
  binop_effect op = ObsR ->
  score_meas (δ2'_partial_deriv_inv op v0) lebesgue_measure =
  pushforward (restrict_meas lebesgue_measure (δ2_dom op v0)) (δ2' op v0).
Proof.
  intros.
  setoid_rewrite <- meas_id_right at 3.
  erewrite change_of_variable; revgoals. {
    apply δ2_deriv; auto.
  } {
    integrand_extensionality v.
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
         (pushforward
            (score_meas (fun x => integration (obs e (v_real x)) μEntropy)
                        (restrict_meas lebesgue_measure (δ1_dom op)))
            (δ1' op) >>= (dirac ∘ v_real)).
      {
        rewrite <- pushforward_as_bind.
        rewrite <- pushforward_compose.
        rewrite pushforward_as_bind.
        unfold restrict_meas, score_meas.
        rewrite !meas_bind_assoc.
        integrand_extensionality x.

        unfold compose.
        cbn.
        rewrite !integration_linear_in_meas.
        rewrite !(meas_id_left x).
        rewrite !integration_linear_in_meas.
        rewrite !(meas_id_left x).

        unfold indicator; cbn.
        destruct δ1; cbn; ring.
      }

      rewrite (push_score _ _ _ _ _ (δ1_bijection op)).
      rewrite <- lebesgue_δ1_invariant.

      rewrite double_score.
      unfold score_meas.
      rewrite meas_bind_assoc.
      integrand_extensionality x.

      rewrite integration_linear_in_meas.
      fold (dirac x).
      rewrite meas_id_left.
      unfold compose, dirac.
      rewrite ennr_mul_comm.
      f_equal.
      unfold δ1'_partial_deriv_inv, δ1'_inv.
      unfold ennr_div.
      destruct δ1_inv; cbn in *; ring.
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

      setoid_rewrite tonelli at 2; auto.
      apply peer_inside_the_μ; auto.
      intros vl _.
      destruct_val vl.
      clear H el.

      replace (μ er)
      with (lebesgue_val_measure
              >>= (fun x A => indicator A x * obs_μ er x full_event));
        revgoals.
      {
        destruct H0 as [_ ?].
        symmetry.
        apply (H eq_refl eq_refl).
      }
      unfold lebesgue_val_measure.
      rewrite bind_of_pushforward.
      rewrite meas_bind_assoc.
      unfold compose.

      unfold obs_μ.
      setoid_rewrite ennr_mul_1_l.
      setoid_rewrite ennr_mul_comm at 1.
      setoid_rewrite integration_linear_in_meas.

      transitivity (
          score_meas
            (fun x => integration (obs er (v_real x)) μEntropy)
            lebesgue_measure >>=
                           (fun (x : R) => binop_in op (v_real r) (v_real x))).
      {
        rewrite bind_of_score.
        integrand_extensionality x.
        fold (dirac (v_real x)).
        rewrite meas_id_left.
        reflexivity.
      }

      transitivity (pushforward
                      (score_meas (fun x => integration (obs er (v_real x)) μEntropy)
                                  (restrict_meas lebesgue_measure (δ2_dom op r)))
                      (δ2' op r) >>= (dirac ∘ v_real)).
      {
        rewrite <- pushforward_as_bind.
        rewrite <- pushforward_compose.
        rewrite pushforward_as_bind.
        unfold restrict_meas, score_meas.
        rewrite !meas_bind_assoc.
        integrand_extensionality x.

        unfold compose.
        rewrite !integration_linear_in_meas.
        rewrite !(meas_id_left x).
        rewrite !integration_linear_in_meas.
        rewrite !(meas_id_left x).

        unfold indicator; cbn.
        destruct δ2; cbn; ring.
      }

      rewrite (push_score _ _ _ _ _ (δ2_bijection op r H1)).
      rewrite <- lebesgue_δ2_invariant; auto.

      rewrite double_score.
      unfold score_meas.
      rewrite meas_bind_assoc.
      integrand_extensionality x.

      rewrite integration_linear_in_meas.
      fold (dirac x).
      rewrite meas_id_left.
      unfold compose, dirac.
      rewrite ennr_mul_comm.
      rewrite <- integration_linear_mult_l.
      f_equal.

      unfold δ2'_partial_deriv_inv.
      cbn.
      destruct δ2_inv; cbn. {
        setoid_rewrite <- integration_linear_mult_r.
        setoid_rewrite ennr_mul_1_l.
        reflexivity.
      } {
        rewrite integration_of_0.
        ring.
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
