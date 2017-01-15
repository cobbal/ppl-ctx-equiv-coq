Require Import Basics.
Require Import Reals.
Require Import List.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import syntax.
Require Import utils.
Require Import Coq.Classes.Morphisms.
Require Import integration.
Import EqNotations.
Require determinism.
Import determinism.eval_dec.

Local Open Scope ennr.

Definition ev {τ} (e : expr · τ) σ : option (val τ) :=
  match eval_dec e σ with
  | eval_dec_ex_unique v w _ _ => Some v
  | eval_dec_not_ex _ => None
  end.

Definition ew {τ} (e : expr · τ) σ : R+ :=
  match eval_dec e σ with
  | eval_dec_ex_unique v w _ _ => w
  | eval_dec_not_ex _ => 0
  end.

Definition eval_in {τ} (e : expr · τ) σ : Meas (val τ) :=
  fun A =>
    option0 (indicator A <$> ev e σ) * ew e σ.

Definition μ {τ} (e : expr · τ) : Meas (val τ) :=
  μEntropy >>= eval_in e.

Ltac fold_μ :=
  match goal with
  | [ |- context [ μEntropy >>= eval_in ?e ] ] => fold (μ e)
  | [ H : context [ μEntropy >>= eval_in ?e ] |- _ ] => fold (μ e)
  end.

Definition A_rel' (τ : Ty) (V_rel_τ : relation (val τ)) : relation (Event (val τ)) :=
  fun A0 A1 =>
    forall v0 v1 (Hv : V_rel_τ v0 v1),
      (A0 v0 = (* iff *) A1 v1).

Definition E_rel' (τ : Ty) (V_rel_τ : relation (val τ)) : relation (expr · τ) :=
  fun e0 e1 =>
    forall A0 A1 (HA : A_rel' τ V_rel_τ A0 A1),
      μ e0 A0 = μ e1 A1.

Definition V_rel_real : relation (val ℝ) := eq.

Inductive V_rel_arrow τa τr
          (V_rel_a : relation (val τa))
          (V_rel_r : relation (val τr))
  : relation (val (τa ~> τr)) :=
| mk_V_rel_arrow (body0 body1 : expr (τa :: ·) τr) :
    (forall (va0 va1 : val τa),
        V_rel_a va0 va1 ->
        E_rel' τr V_rel_r
               (proj1_sig (ty_subst1 body0 va0))
               (proj1_sig (ty_subst1 body1 va1))) ->
      V_rel_arrow τa τr V_rel_a V_rel_r
                  (v_lam body0)
                  (v_lam body1).
Arguments mk_V_rel_arrow {_ _ _ _ _ _} Hva.

Fixpoint V_rel τ : relation (val τ) :=
  match τ with
  | ℝ => V_rel_real
  | τa ~> τr => V_rel_arrow τa τr (V_rel τa) (V_rel τr)
  end.

Definition A_rel τ := A_rel' τ (V_rel τ).
Definition E_rel τ := E_rel' τ (V_rel τ).

Inductive G_rel : forall Γ, relation (wt_env Γ) :=
| G_rel_nil : G_rel · dep_nil dep_nil
| G_rel_cons {τ Γ v0 v1 ρ0 ρ1} :
    V_rel τ v0 v1 -> G_rel Γ ρ0 ρ1 ->
    G_rel (τ :: Γ) (dep_cons v0 ρ0) (dep_cons v1 ρ1).

Lemma apply_G_rel {Γ ρ0 ρ1} :
  G_rel Γ ρ0 ρ1 ->
  forall {x τ} {v0 v1 : val τ},
    lookup Γ x = Some τ ->
    erase v0 = erase_wt_env ρ0 x ->
    erase v1 = erase_wt_env ρ1 x ->
    V_rel τ v0 v1.
Proof.
  intros.
  revert Γ ρ0 ρ1 H H0 H1 H2.
  induction x; intros. {
    dep_destruct (Γ, H0).
    dep_destruct (ρ0, ρ1, H1, H2).
    dep_destruct H.

    cbn in *.
    elim_erase_eqs.
    apply val_eq in x0.
    apply val_eq in x.
    subst.
    auto.
  } {
    dep_destruct (Γ, H0).
    dep_destruct (ρ0, ρ1, H1, H2).
    dep_destruct H.
    eapply IHx; eauto.
  }
Qed.

Definition related_exprs Γ τ : relation (expr Γ τ) :=
  fun e0 e1 =>
    forall ρ0 ρ1 (Hρ : G_rel Γ ρ0 ρ1),
      E_rel τ (proj1_sig (close ρ0 e0)) (proj1_sig (close ρ1 e1)).

Notation "'EXP' Γ ⊢ e0 ≈ e1 : τ" :=
  (related_exprs Γ τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, no associativity).

Ltac econtradict e := exfalso; eapply e; repeat econstructor; eauto.

Ltac decide_eval' e σ v w ex u :=
  let not_ex := fresh "not_ex" in
  let focus_ev := fresh "focus_ev" in
  let focus_ew := fresh "focus_ew" in
  set (focus_ev := ev e σ);
  set (focus_ew := ew e σ);
  unfold ev in focus_ev;
  unfold ew in focus_ew;
  destruct (eval_dec e σ) as [v w ex u | not_ex];
  subst focus_ev focus_ew;
  [| try solve [ econtradict not_ex
               | Finite
               | ring]
  ].

Tactic Notation "decide_eval" "as"
       "[" ident(v) ident(w) ident(ex) ident(u) "]"
  := match goal with
     | [ |- context[ev ?e ?σ] ] => decide_eval' e σ v w ex u
     end.
Tactic Notation "decide_eval" constr(e) constr(σ) "as"
       "[" ident(v) ident(w) ident(ex) ident(u) "]"
  :=  decide_eval' e σ v w ex u.

Ltac what_equality_am_I_proving :=
  match goal with
  | [ |- @eq ?t ?l ?r ] => idtac "proving" l "=" r "at type" t
  | _ => idtac "it doesn't look like your goal is an equality"
  end.

Lemma val_is_atomic {τ} (v : val τ) A σ :
  eval_in v σ A =
  indicator A v.
Proof.
  unfold eval_in.

  decide_eval as [v' w ex u]; simpl. {
    destruct (invert_eval_val ex).
    subst.
    ring.
  }
Qed.

Lemma val_is_dirac {τ} (v : val τ) :
  μ v = dirac v.
Proof.
  extensionality A.
  unfold μ, dirac; simpl.
  apply integration_const_entropy; intro σ.
  erewrite val_is_atomic.
  reflexivity.
Qed.

Lemma compat_real Γ r :
  (EXP Γ ⊢ e_real r ≈ e_real r : ℝ).
Proof.
  repeat intro.
  elim_sig_exprs.
  elim_erase_eqs.

  rewrite rewrite_v_real.
  rewrite val_is_dirac.
  unfold dirac, indicator.
  f_equal.
  apply HA.

  hnf.
  reflexivity.
Qed.

Lemma compat_var Γ x τ
      (Hx : lookup Γ x = Some τ) :
  EXP Γ ⊢ e_var x Hx ≈ e_var x Hx : τ.
Proof.
  repeat intro.
  elim_sig_exprs.

  destruct (env_search_subst ρ0 Hx) as [v0 ρ0x].
  destruct (env_search_subst ρ1 Hx) as [v1 ρ1x].

  pose proof (apply_G_rel Hρ Hx ρ0x ρ1x).
  elim_erase_eqs.

  rewrite 2 val_is_dirac.
  unfold dirac, indicator.
  f_equal.
  exact (HA _ _ H).
Qed.

Lemma compat_lam Γ τa τr body0 body1 :
  (EXP (τa :: Γ) ⊢ body0 ≈ body1 : τr) ->
  (EXP Γ ⊢ e_lam body0 ≈ e_lam body1 : (τa ~> τr)).
Proof.
  repeat intro.
  elim_sig_exprs.
  elim_erase_eqs.

  rewrite 2 rewrite_v_lam.
  rewrite 2 val_is_dirac.

  unfold dirac, indicator.
  f_equal.
  apply HA.

  constructor.
  intros.

  specialize (H (dep_cons va0 ρ0) (dep_cons va1 ρ1) (G_rel_cons H0 Hρ)).

  elim_sig_exprs.
  elim_erase_eqs.
  asimpl in He3.
  asimpl in He4.
  elim_erase_eqs.

  apply H.
Qed.

Theorem μe_as_pushforard {τ} (e : expr · τ) :
  μ e = meas_option (pushforward (score_meas (ew e) μEntropy) (ev e)).
Proof.
  intros.

  extensionality A.
  unfold μ, meas_bind, meas_option, pushforward, score_meas, compose, preimage, eval_in.
  setoid_rewrite riemann_def_of_lebesgue_integration.
  integrand_extensionality t.
  f_equal.
  extensionality σ.

  unfold indicator.
  rewrite ennr_mul_comm.
  destruct ev; auto.
Qed.

Lemma μ_interchangable {τ0 τ1} (e0 : expr · τ0) (e1 : expr · τ1) : interchangable (μ e0) (μ e1).
Proof.
  repeat intro.
  rewrite 2 μe_as_pushforard.

  apply meas_option_interchangable.
  apply pushforward_interchangable.
  apply score_meas_interchangable.
  apply interchangable_sym.
  apply meas_option_interchangable.
  apply pushforward_interchangable.
  apply score_meas_interchangable.
  apply sigma_finite_is_interchangable; auto.
Qed.

Theorem μe_eq_μEntropy :
  forall {τ B} (e : expr · τ)
         (f : val τ -> Meas B),
    μ e >>= f =
    μEntropy >>=
             (fun σ A =>
                option0 ((fun v => f v A) <$> ev e σ) * ew e σ).
Proof.
  intros.

  unfold μ, ">>=".

  extensionality A.

  rewrite riemann_def_of_lebesgue_integration.
  rewrite tonelli_sigma_finite; auto.
  unfold eval_in.

  integrand_extensionality σ.

  rewrite <- integration_linear_mult_r.
  f_equal.

  destruct (ev _ _); simpl. {
    setoid_rewrite integration_of_indicator.
    apply lebesgue_pos_measure_interval.
  } {
    apply integration_of_0.
  }
Qed.

(* used to push the option0 into the very inside *)
Lemma μe_eq_μEntropy2 {τ0 τ1 B}
      (f : val τ0 -> val τ1 -> Meas B)
      (e0 : expr · τ0) (e1 : expr · τ1) :
  μ e0 >>= (fun v0 => μ e1 >>= (fun v1 => f v0 v1)) =
  μEntropy >>=
           (fun σ0 =>
              μEntropy >>=
                       (fun σ1 A =>
                          option0 ((fun v0 v1 => f v0 v1 A)
                                     <$> ev e0 σ0 <*> ev e1 σ1)
                                  * ew e1 σ1 * ew e0 σ0)).
Proof.
  extensionality A.
  setoid_rewrite μe_eq_μEntropy; eauto.
  rewrite μe_eq_μEntropy.
  integrand_extensionality σ0.

  unfold ">>=".
  rewrite <- integration_linear_mult_r.
  f_equal.

  decide_eval as [v0 w0 ex0 u0]; simpl; auto.
  rewrite <- integration_linear_mult_l.
  ring.
Qed.

Definition plus_in (v v' : val ℝ) : Meas (val ℝ) :=
    match (v : expr · ℝ), (v' : expr · ℝ) with
    | e_real r, e_real r' => fun A => indicator A (v_real (r + r'))
    | _, _ => fun A => 0
    end.

Lemma by_μe_eq_μEntropy_plus (el er : expr · ℝ) :
  μ (e_plus el er) =
  μ el >>= (fun vl => μ er >>= (fun vr => plus_in vl vr)).
Proof.
  extensionality A.

  rewrite μe_eq_μEntropy2.
  set (f σ0 σ1 A :=
         option0 (((fun vl vr => plus_in vl vr A) <$> ev el σ0) <*> ev er σ1)
                 * ew er σ1 * ew el σ0).
  transitivity ((μEntropy >>= (fun σ => f (π 0 σ) (π 1 σ))) A). {
    subst f.
    simpl.

    integrand_extensionality σ.

    unfold eval_in.
    decide_eval (e_plus el er) σ as [v0 w0 ex0 u0]. {
      dependent destruction ex0; try absurd_val.
      decide_eval el (π 0 σ) as [vl wl exl ul].
      decide_eval er (π 1 σ) as [vr wr exr ur].
      destruct_val vr.
      destruct_val vl.
      simpl.

      destruct (ul _ _ ex0_1), (ur _ _ ex0_2); subst.
      dep_destruct (H, H1).

      unfold plus_in; simpl.
      ring.
    } {
      decide_eval el (π 0 σ) as [vl wl exl ul].
      decide_eval er (π 1 σ) as [vr wr exr ur].
      destruct_val vr.
      destruct_val vl.
      econtradict not_ex.
    }
  } {
    rewrite pick_2_entropies.
    auto.
  }
Qed.

Lemma work_of_plus
      {el0 er0 el1 er1 : expr · ℝ}
      (Hl : forall Al0 Al1,
          A_rel ℝ Al0 Al1 ->
          μ el0 Al0 = μ el1 Al1)
      (Hr : forall Ar0 Ar1,
          A_rel ℝ Ar0 Ar1 ->
          μ er0 Ar0 = μ er1 Ar1)
      {A0 A1} (HA : A_rel ℝ A0 A1)
  : μ (e_plus el0 er0) A0 = μ (e_plus el1 er1) A1.
Proof.
  do 2 rewrite by_μe_eq_μEntropy_plus.

  apply (coarsening (A_rel ℝ)); auto.
  intros B vl0 vl1 Hvl.
  unfold preimage.
  f_equal.

  apply (coarsening (A_rel ℝ)); auto.
  intros B0 vr0 vr1 Hvr.
  unfold preimage.
  f_equal.

  destruct_val vl0.
  destruct_val vl1.
  destruct_val vr0.
  destruct_val vr1.

  hnf in Hvl, Hvr.
  dep_destruct (Hvl, Hvr).
  unfold plus_in; simpl.

  unfold indicator.
  f_equal.
  apply HA.
  reflexivity.
Qed.

Lemma compat_plus Γ el0 er0 el1 er1 :
  (EXP Γ ⊢ el0 ≈ el1 : ℝ) ->
  (EXP Γ ⊢ er0 ≈ er1 : ℝ) ->
  (EXP Γ ⊢ e_plus el0 er0 ≈ e_plus el1 er1 : ℝ).
Proof.
  intros Hl Hr.

  repeat intro.

  specialize (Hl _ _ Hρ).
  specialize (Hr _ _ Hρ).

  elim_sig_exprs.
  dep_destruct (e3, He3).
  dep_destruct (e4, He4).
  elim_erase_eqs.

  apply work_of_plus; auto.
Qed.

Definition apply_in {τa τr} (vf : val (τa ~> τr)) (va : val τa) :
  Entropy -> Meas (val τr) :=
  match (vf : expr _ _) in (expr _ τ)
        return (τ = τa ~> τr -> Entropy -> Meas (val τr))
  with
  | e_lam body => fun H => ltac:(inject H; refine (eval_in (proj1_sig (ty_subst1 body va))))
  | _ => (* this will never happen, but "0" is easier to use than False_rect here *)
    fun _ _ => empty_meas _
  end eq_refl.

Lemma by_μe_eq_μEntropy_app {τa τr}
      (ef : expr · (τa ~> τr))
      (ea : expr · τa) :
  μ (e_app ef ea) =
  μ ef >>= (fun vf => μ ea >>= (fun va => μEntropy >>= apply_in vf va)).
Proof.
  extensionality A.

  rewrite μe_eq_μEntropy2.
  set (x σf σa σbody A :=
         option0 ((fun vf va => apply_in vf va σbody A)
                    <$> ev ef σf
                    <*> ev ea σa)
                 * ew ea σa * ew ef σf).
  transitivity ((μEntropy >>= (fun σ => x (π 0 σ) (π 1 σ) (π 2 σ))) A). {
    subst x.
    simpl.

    integrand_extensionality σ.

    unfold eval_in.
    decide_eval (e_app ef ea) σ as [vr wr exr ur]; simpl. {
      dep_destruct exr; try absurd_val.
      rename va into va'.
      decide_eval ef (π 0 σ) as [vf wf exf uf].
      decide_eval ea (π 1 σ) as [va wa exa ua].
      simpl.

      destruct_val vf.
      cbn.

      destruct (uf _ _ exr1), (ua _ _ exr2); subst.
      dep_destruct H.

      unfold eval_in.

      decide_eval as [vr' wr' exr' ur'].
      destruct (ur' _ _ exr3); subst.
      simpl.
      ring.
    } {
      decide_eval ef (π 0 σ) as [vf wf exf uf].
      decide_eval ea (π 1 σ) as [va wa exa ua].
      simpl.

      destruct_val vf.
      cbn.

      unfold eval_in.

      decide_eval as [v5 w5 ex5 u5].
      econtradict not_ex.
    }
  } {
    rewrite pick_3_entropies.
    integrand_extensionality σf.
    integrand_extensionality σa.
    subst x.
    simpl.
    unfold ">>=".
    rewrite <- 2 integration_linear_mult_r.
    do 2 f_equal.

    decide_eval ef σf as [vf wf exf uf]; simpl. {
      decide_eval ea σa as [va wa exa ua]; simpl; auto.
      apply integration_const_entropy; auto.
    } {
      apply integration_const_entropy; auto.
    }
  }
Qed.

Lemma work_of_app {τa τr}
      (ef0 ef1 : expr · (τa ~> τr))
      (ea0 ea1 : expr · τa)
      (Hf : forall Af0 Af1 : Event (val (τa ~> τr)),
          A_rel (τa ~> τr) Af0 Af1 ->
          μ ef0 Af0 = μ ef1 Af1)
      (Ha : forall Aa0 Aa1 : Event (val τa),
          A_rel τa Aa0 Aa1 ->
          μ ea0 Aa0 = μ ea1 Aa1)
      {A0 A1 : Event (val τr)}
      (HA : A_rel τr A0 A1)
  : μ (e_app ef0 ea0) A0 = μ (e_app ef1 ea1) A1.
Proof.
  do 2 rewrite by_μe_eq_μEntropy_app.

  apply (coarsening (A_rel (τa ~> τr))); auto.
  intros B vf0 vf1 Hvf.
  unfold preimage.
  f_equal.

  apply (coarsening (A_rel τa)); auto.
  intros B0 va0 va1 Hva.
  unfold preimage.
  f_equal.

  destruct_val vf0.
  destruct_val vf1.

  destruct Hvf as [? ? Hvf].
  clear body body0.

  specialize (Hvf _ _ Hva _ _ HA).
  apply Hvf.
Qed.

Lemma compat_app Γ τa τr ef0 ef1 ea0 ea1 :
  (EXP Γ ⊢ ef0 ≈ ef1 : (τa ~> τr)) ->
  (EXP Γ ⊢ ea0 ≈ ea1 : τa) ->
  (EXP Γ ⊢ e_app ef0 ea0 ≈ e_app ef1 ea1 : τr).
Proof.
  intros Hf Ha.

  repeat intro.

  specialize (Hf _ _ Hρ).
  specialize (Ha _ _ Hρ).

  elim_sig_exprs.
  elim_erase_eqs.

  apply work_of_app; auto.
Qed.

Lemma compat_sample Γ :
  EXP Γ ⊢ e_sample ≈ e_sample : ℝ.
Proof.
  repeat intro.

  elim_sig_exprs.
  elim_erase_eqs.

  f_equal.
  extensionality v.

  apply HA.
  reflexivity.
Qed.

Definition factor_in (v : val ℝ) : Meas (val ℝ) :=
  fun A =>
    match (v : expr · ℝ) with
    | e_real r =>
      match Rle_dec 0 r with
      | left rpos => indicator A (v_real r) * finite r rpos
      | _ => 0
      end
    | _ => 0
    end.

Lemma by_μe_eq_μEntropy_factor (e : expr · ℝ) :
  μ (e_factor e) =
  μ e >>= factor_in.
Proof.
  extensionality A.

  rewrite μe_eq_μEntropy.

  integrand_extensionality σ.
  unfold eval_in.

  decide_eval (e_factor e) σ as [vr wr exr ur]; simpl. {
    destruct_val vr.
    dep_destruct exr; try absurd_val.

    decide_eval as [ve we exe ue].
    destruct (ue _ _ exr); subst.

    unfold factor_in; simpl.
    destruct Rle_dec; [| contradiction].
    replace (finite r r0) with (finite r rpos) by Finite.
    ring.
  } {
    decide_eval as [ve we exe ue].
    destruct_val ve.
    unfold factor_in; simpl.

    destruct Rle_dec; [| solve [ring]].
    econtradict not_ex.
    Unshelve.
    auto.
  }
Qed.

Lemma work_of_factor
  (e0 e1 : expr · ℝ)
  (He : forall A0 A1 : Event (val ℝ),
      A_rel' ℝ (V_rel ℝ) A0 A1 ->
      μ e0 A0 = μ e1 A1)
  (A0 A1 : Event (val ℝ))
  (HA : A_rel' ℝ (V_rel ℝ) A0 A1) :
  μ (e_factor e0) A0 = μ (e_factor e1) A1.
Proof.
  rewrite 2 by_μe_eq_μEntropy_factor.

  apply (coarsening (A_rel ℝ)); auto.
  intros B v0 v1 Hv.
  unfold preimage.
  f_equal.

  destruct_val v0.
  destruct_val v1.
  simpl in *.
  dep_destruct Hv.

  unfold factor_in; simpl.
  destruct Rle_dec; auto.

  unfold indicator.
  do 2 f_equal.
  apply HA.
  reflexivity.
Qed.

Lemma compat_factor Γ e0 e1:
  (EXP Γ ⊢ e0 ≈ e1 : ℝ) ->
  (EXP Γ ⊢ e_factor e0 ≈ e_factor e1 : ℝ).
Proof.
  repeat intro.

  specialize (H _ _ Hρ).

  elim_sig_exprs.
  elim_erase_eqs.

  apply work_of_factor; auto.
Qed.

Lemma fundamental_property {Γ τ} (e : expr Γ τ) :
  (EXP Γ ⊢ e ≈ e : τ).
Proof.
  induction e.
  - apply compat_real.
  - apply compat_var.
  - apply compat_lam; auto.
  - apply compat_app; auto.
  - apply compat_factor; auto.
  - apply compat_sample.
  - apply compat_plus; auto.
Qed.

Print Assumptions fundamental_property.

Lemma fundamental_property_of_values {τ} (v : val τ) :
  V_rel τ v v.
Proof.
  intros.

  destruct v using wt_val_rect; subst; simpl in *. {
    reflexivity.
  } {
    constructor.
    repeat intro.

    pose proof fundamental_property body as fp.
    specialize (fp _ _ (G_rel_cons H G_rel_nil)).

    elim_sig_exprs.
    elim_erase_eqs.

    apply fp; auto.
  }
Qed.
