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
  integrand_extensionality x.
  setoid_rewrite ennr_mul_comm.
  rewrite integration_linear_in_meas.
  fold (dirac x).
  rewrite meas_id_left.
  trivial.
Qed.

Lemma scale_deriv r :
  (r <> R0) ->
  is_RN_deriv
    (pushforward lebesgue_measure (Rmult r))
    lebesgue_measure
    (const (ennr_abs (/ r))).
Proof.
  intros.
  simple refine (RN_deriv_is_coq_deriv _ (Rmult (/ r)%R) _ _ _ _ _); intros. {
    apply derivable_mult; [apply derivable_const | apply derivable_id].
  } {
    field; auto.
  } {
    field; auto.
  } {
    unfold const.
    f_equal.
    unfold derive, derive_pt, const.
    destruct derivable_mult; cbn.
    unfold derivable_pt_abs in d.
    unfold mult_fct in *.
    enough (r = x0). {
      subst.
      unfold ennr_abs; cbn.
      destruct Req_EM_T. {
        exfalso.
        unfold Rabs in e.
        destruct Rcase_abs; subst; try fourier; tauto.
      }
      ennr.
      apply Rabs_Rinv; auto.
    }
    eapply uniqueness_limite; eauto.
    repeat intro.
    assert (0 < (2 * eps))%R by fourier.
    exists (mkposreal _ H0).
    intros.
    cbn in *.
    replace (Rabs _) with (Rabs 0%R) by (f_equal; field; auto).
    unfold Rabs.
    destruct Rcase_abs; try fourier.
  }
Qed.

Lemma lebesgue_scale r :
  r <> R0 ->
  lebesgue_measure = (fun A : Event R => ennr_abs r * pushforward lebesgue_measure (Rmult r) A).
Proof.
  intros.
  rewrite <- (meas_id_right (pushforward lebesgue_measure (Rmult r))).
  erewrite change_of_variable; [| apply scale_deriv; auto].
  unfold pushforward, compose, preimage.
  extensionality A.
  unfold const.
  setoid_rewrite <- integration_linear_mult_r.
  unfold dirac.
  rewrite integration_of_indicator.

  rewrite ennr_mul_comm.
  rewrite <- ennr_mul_assoc.
  rewrite <- ennr_mul_1_r at 1.
  f_equal.
  ennr.
  unfold Rabs.
  repeat destruct Rcase_abs; try field; auto. {
    exfalso.
    assert (0 <= r)%R by fourier.
    pose proof nnr.Rinv_pos H0 ltac:(auto).
    pose proof Rle_lt_trans _ _ _ H1 r0.
    econtradict Rlt_irrefl.
  } {
    assert (0 <= / r)%R by (set (/ r)%R in *; fourier).
    assert (0 <= r)%R. {
      rewrite <- Rinv_involutive; auto.
      apply nnr.Rinv_pos; auto.
      intro.
      symmetry in H1.
      apply Rinv_neq_0_compat in H1; auto.
    }
    pose proof Rle_lt_trans _ _ _ H1 r1.
    fourier.
  }
Qed.

Lemma plus_deriv r : is_RN_deriv
                       (pushforward lebesgue_measure (Rplus r))
                       lebesgue_measure
                       (const 1).
Proof.
  simple refine (RN_deriv_is_coq_deriv _ (fun x => x - r) _ _ _ _ _); intros; cbn. {
    apply derivable_plus; [apply derivable_const | apply derivable_id].
  } {
    ring.
  } {
    ring.
  }
  unfold const.
  ring_simplify.
  unfold derive, derive_pt, const.
  destruct derivable_plus; cbn.
  unfold derivable_pt_abs in d.
  unfold plus_fct in *.
  enough (x0 = 1)%R. {
    subst.
    unfold ennr_abs; cbn.
    destruct Req_EM_T. {
      unfold Rabs in e.
      destruct Rcase_abs; fourier.
    }
    ennr.
    unfold Rabs.
    destruct Rcase_abs; auto; try fourier; field.
  } {
    eapply uniqueness_limite; eauto.
    repeat intro.
    exists (mkposreal _ H).
    intros.
    cbn in *.
    replace (Rabs _)%R with (Rabs 0)%R by (f_equal; field; auto).
    unfold Rabs.
    destruct Rcase_abs; fourier.
  }
Qed.

Lemma lebesgue_translate_invariant r :
  lebesgue_measure = pushforward lebesgue_measure (Rplus r).
Proof.
  rewrite <- (meas_id_right (pushforward lebesgue_measure (Rplus r))).
  erewrite change_of_variable; [| apply (plus_deriv r)].
  unfold const.
  setoid_rewrite ennr_mul_1_r.
  rewrite meas_id_right.
  auto.
Qed.

Definition score_meas {X} (w : X -> R+) (μ : Meas X) : Meas X :=
  μ >>= (fun x A => w x * indicator A x).

Definition score_abs_meas {X} (w : X -> R) (μ : Meas X) : Meas X :=
  μ >>= (fun x A => ennr_abs (w x) * indicator A x).

Lemma bind_of_score_abs {A B} w μ (f : A -> Meas B) :
  score_abs_meas w μ >>= f = μ >>= (fun a ev => ennr_abs (w a) * f a ev).
Proof.
  unfold score_abs_meas.
  rewrite meas_bind_assoc.
  integrand_extensionality x.
  rewrite integration_linear_in_meas.
  fold (dirac x).
  rewrite meas_id_left.
  reflexivity.
Qed.

Lemma bind_of_score {A B} w μ (f : A -> Meas B) :
  score_meas w μ >>= f = μ >>= (fun a ev => (w a) * f a ev).
Proof.
  unfold score_meas.
  rewrite meas_bind_assoc.
  integrand_extensionality x.
  rewrite integration_linear_in_meas.
  fold (dirac x).
  rewrite meas_id_left.
  reflexivity.
Qed.

Lemma push_score {X Y} (f : X -> R+) (g : X -> Y) (g_inv : Y -> X) (μ : Meas X) :
  (forall x : X, g_inv (g x) = x) ->
  pushforward (score_meas f μ) g =
  score_meas (f ∘ g_inv) (pushforward μ g).
Proof.
  intros.
  unfold score_meas.
  (* rewrite bind_of_pushforward. *)
  unfold compose.
  rewrite 2 pushforward_as_bind.
  repeat rewrite meas_bind_assoc.
  integrand_extensionality x.
  unfold compose.
  rewrite meas_id_left.
  rewrite integration_linear_in_meas.
  fold (dirac x).
  rewrite meas_id_left.
  rewrite H.
  auto.
Qed.

Lemma δ_deriv op v0 :
    is_RN_deriv
      (pushforward lebesgue_measure (δ op v0))
      lebesgue_measure
      (fun x => / ennr_abs (δ_partial_deriv_2 op v0 (fromOption R0 (δ_unique_inv op v0 x)))).
      (* (fun x => ennr_abs (/ δ_partial_deriv_2 op v0 x)). *)
Proof.
  refine (RN_deriv_is_coq_deriv
            _
            (fun x => fromOption R0 (δ_unique_inv op v0 x))
            _
            (δ_derivable _ _)
            _ _ _);
    auto;
    cbn;
    intros;
    revgoals.
  {
    rewrite δ_inv_get_away_with_cheating.
    cbn.
    apply δ_inv_cheat_left.
  } {
    rewrite δ_inv_get_away_with_cheating.
    cbn.
    apply δ_inv_cheat_right.
  }
Qed.

Lemma lebesgue_deriv_invariant op v0 :
  score_meas
    (ennr_inv ∘ ennr_abs ∘ δ_partial_deriv_2 op v0 ∘ δ_unique_inv_cheating op v0)
    lebesgue_measure =
  pushforward lebesgue_measure (δ op v0).
Proof.
  setoid_rewrite <- (meas_id_right (pushforward lebesgue_measure (δ op v0))).
  erewrite change_of_variable; revgoals. {
    apply δ_deriv.
  } {
    unfold compose.
    integrand_extensionality x.
    unfold dirac.
    rewrite δ_inv_get_away_with_cheating.
    cbn.
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
                           (fun (x : R) => op_in op (v_real r) (v_real x))).
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

      rewrite <- (pushforward_as_bind _ (v_real ∘ δ op r)).
      rewrite pushforward_compose.


      rewrite <- meas_id_right at 1.
      rewrite bind_of_pushforward.

      setoid_rewrite <- integration_linear_mult_l.

      erewrite push_score; try apply δ_inv_cheat_left.
      rewrite bind_of_score.
      rewrite <- lebesgue_deriv_invariant.

      rewrite bind_of_score.
      integrand_extensionality x.
      unfold compose.
      rewrite ennr_mul_assoc.
      rewrite ennr_mul_comm.
      f_equal.
      rewrite δ_inv_get_away_with_cheating.
      rewrite integration_linear_mult_l.
      integrand_extensionality σ.
      unfold ennr_div.
      cbn.
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
