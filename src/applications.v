Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.

Require Import utils.
Require Import syntax.
Require Import relations.
Require Import ctxequiv.
Require Import properties_of_relations.
Require Import integration.

Local Open Scope nat.

Transparent π.

Notation "'λ,' e" := (e_lam e) (at level 69, right associativity).
Infix "@" := e_app (at level 68, left associativity).
Infix "+!" := e_plus.

Definition var_0 {τ Γ} : expr (τ :: Γ) τ :=
  e_var O (eq_refl : lookup (τ :: Γ) O = Some τ).
Definition var_1 {τ0 τ1 Γ} : expr (τ0 :: τ1 :: Γ) τ1 :=
  e_var 1%nat (eq_refl : lookup (τ0 :: τ1 :: Γ) 1%nat = Some τ1).

(** Since our program measure is just a re-weighted pushforward, it's interchangable *)
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

Instance μ_interchangable {τ0 τ1} (e0 : expr · τ0) (e1 : expr · τ1) : interchangable (μ e0) (μ e1).
Proof.
  repeat intro.
  rewrite 2 μe_as_pushforard.

  apply meas_option_interchangable, pushforward_interchangable, score_meas_interchangable.
  apply interchangable_sym.
  apply meas_option_interchangable, pushforward_interchangable, score_meas_interchangable.
  apply sigma_finite_is_interchangable; auto.
Qed.

(** Alternative proof *)
Lemma μ_interchangable' {τ0 τ1} (e0 : expr · τ0) (e1 : expr · τ1) : interchangable (μ e0) (μ e1).
Proof.
  repeat intro.
  setoid_rewrite μe_eq_μEntropy2.
  rewrite sigma_finite_is_interchangable; auto.

  extensionality A.
  integrand_extensionality σ0.
  integrand_extensionality σ1.
  rewrite <- !ennr_mul_assoc.
  f_equal; try ring.
  repeat destruct ev; cbn; auto.
Qed.

Lemma πL_same_integral f :
  integration (f ∘ πL) μEntropy = integration f μEntropy.
Proof.
  replace (f ∘ πL) with (fun σ => block (fun σL σR => f σL) (πL σ) (πR σ)) by auto.
  rewrite integration_πL_πR.
  unfold block.
  simpl.
  f_equal.
  extensionality σ.
  apply integration_const_entropy; auto.
Qed.

Lemma πR_same_integral f :
  integration (f ∘ πR) μEntropy = integration f μEntropy.
Proof.
  replace (f ∘ πR) with (fun σ => block (fun σL σR => f σR) (πL σ) (πR σ)) by auto.
  rewrite integration_πL_πR.
  unfold block.
  simpl.
  apply integration_const_entropy; auto.
Qed.

Lemma project_same_integral f n :
  integration (f ∘ π n) μEntropy = integration f μEntropy.
Proof.
  induction n. {
    unfold π.
    apply πL_same_integral.
  } {
    rewrite <- IHn.
    clear IHn.
    replace (f ∘ π (S n)) with (f ∘ π n ∘ πR) by auto.
    apply πR_same_integral.
  }
Qed.

Lemma subst_val {τ B} (v : val τ) (f : val τ -> Meas B) :
  μ v >>= f = f v.
Proof.
  rewrite val_is_dirac.
  apply meas_id_left.
Qed.

Lemma subst_lam {τa τr B} e (f : val (τa ~> τr) -> Meas B) :
  μ (λ, e) >>= f = f (v_lam e).
Proof.
  rewrite rewrite_v_lam.
  apply subst_val.
Qed.

Lemma subst_real {B} r (f : val ℝ -> Meas B) :
  μ (e_real r) >>= f = f (v_real r).
Proof.
  rewrite rewrite_v_real.
  apply subst_val.
Qed.

Definition e_let {Γ τ0 τ1} (e0 : expr Γ τ0) (e1 : expr (τ0 :: Γ) τ1) := (λ, e1) @ e0.

Goal forall {τ0 τ1} (e0 : expr · τ0) (e1 : expr _ τ1),
    μ (e_let e0 e1) =
    μ e0 >>= (fun va => μ (proj1_sig (ty_subst1 e1 va))).
Proof.
  intros.
  unfold e_let.
  rewrite apply_as_transformer.
  rewrite rewrite_v_lam.
  rewrite val_is_dirac.
  rewrite meas_id_left.
  auto.
Qed.

Lemma compat_let {Γ τ τr} e0 e1 er0 er1 :
  (EXP Γ ⊢ e0 ≈ e1 : τ) ->
  (EXP (τ :: Γ) ⊢ er0 ≈ er1 : τr) ->
  (EXP Γ ⊢ e_let e0 er0 ≈ e_let e1 er1 : τr).
Proof.
  intros.
  apply compat_app; auto.
  apply compat_lam; auto.
Qed.

Definition let_in {τ τr} (v : val τ) (body : expr (τ :: ·) τr) :
  Entropy -> Meas (val τr) :=
  eval_in (proj1_sig (ty_subst1 body v)).
Arguments let_in /.

Lemma let_as_transformer {τ τr} (e : expr · τ) (b : expr (τ :: ·) τr) :
  μ (e_let e b) = μ e >>= (fun v => μEntropy >>= let_in v b).
Proof.
  setoid_rewrite apply_as_transformer.
  rewrite subst_lam.
  reflexivity.
Qed.

Ltac fold_let :=
  match goal with
  | [ |- context [(λ, ?b) @ ?e]] => fold (e_let e b)
  | [ H : context [(λ, ?b) @ ?e] |- _] => fold (e_let e b)
  end.

(* TODO: find a real name *)
Ltac munge :=
  progress repeat (cbn;
                   rewrite ?subst_val, ?subst_lam, ?subst_real;
                   try elim_sig_exprs;
                   try elim_erase_eqs;
                   repeat fold_μ;
                   repeat fold_let
                  ).

(** Now the actual theorems *)
Lemma add_zero_related (e : expr · ℝ) :
  (EXP · ⊢ e_real 0 +! e ≈ e : ℝ).
Proof.
  apply relate_exprs; intros.

  munge.
  rewrite plus_as_transformer.
  rewrite subst_real.

  assert (plus_in (v_real 0) = dirac). {
    clear.
    extensionality v.
    destruct_val v.
    unfold plus_in; simpl.
    replace (0 + r)%R with r by ring.
    auto.
  }

  rewrite H.
  rewrite meas_id_right.
  reflexivity.
Qed.

Lemma add_comm_related Γ (e0 e1 : expr Γ ℝ) :
  (EXP Γ ⊢ e0 +! e1 ≈ e1 +! e0 : ℝ).
Proof.
  apply relate_exprs; intros.

  munge.
  rewrite 2 plus_as_transformer.
  rewrite μ_interchangable.
  integrand_extensionality v1.
  integrand_extensionality v0.

  destruct_val v0.
  destruct_val v1.
  cbn.
  rewrite Rplus_comm.
  reflexivity.
Qed.

Program Fixpoint dep_ids' (Γ0 Γ1 : Env Ty) : dep_list (expr (Γ0 ++ Γ1)) Γ1 :=
  match Γ1 return dep_list (expr (Γ0 ++ Γ1)) Γ1 with
  | nil => dep_nil
  | τ :: Γ1' =>
    dep_cons
      (e_var (length Γ0) _)
      (rew <- [fun z => dep_list (expr z) _] (app_assoc Γ0 (τ :: nil) Γ1') in
          dep_ids' (Γ0 ++ τ :: nil) Γ1')
  end.
Next Obligation.
  induction Γ0; auto.
Qed.

Definition dep_ids := dep_ids' ·.

Lemma erase_eq (Γ Γ0 Γ1 : Env Ty)
      (d0 : dep_list (expr Γ0) Γ)
      (d1 : dep_list (expr Γ1) Γ)
      (HΓ : Γ0 = Γ1)
  :
    (d0 ~= d1) ->
    @erase_wt_expr_env Γ Γ0 d0 =
    @erase_wt_expr_env Γ Γ1 d1.
Proof.
  intros.
  subst.
  subst.
  auto.
Qed.

Lemma dep_ids_ids Γ x τ :
  lookup Γ x = Some τ ->
  erase_wt_expr_env (dep_ids Γ) x = ids x.
Proof.
  intros.

  enough (forall Γ0, erase_wt_expr_env (dep_ids' Γ0 Γ) x = u_var (length Γ0 + x)). {
    apply H0.
  }

  intros.
  revert Γ Γ0 H.
  induction x; intros. {
    destruct Γ; inversion H; subst.
    simpl.
    auto.
  } {
    destruct Γ; inversion H; subst.
    simpl in *.
    specialize (IHx Γ (Γ0 ++ t :: nil) H).

    set (dep_ids' _ _) in *.
    clearbody d.
    rewrite app_length, <- plus_assoc in IHx.
    simpl in *.
    rewrite <- IHx.
    clear.

    erewrite erase_eq; auto. {
      rewrite <- app_assoc.
      auto.
    }

    unfold eq_rect_r.
    set (eq_sym _).
    clearbody e.
    dep_destruct e.
    auto.
  }
Qed.

Program Definition open_subst1 {Γ τa τr}
        (e : expr (τa :: Γ) τr)
        (esub : expr Γ τa) :
  { e' : expr Γ τr |
    erase e' = (erase e).[erase esub /] }
  :=
    exist _ (proj1_sig (ty_subst e Γ (dep_cons esub (dep_ids _)))) _.
Next Obligation.
  elim_sig_exprs.
  rewrite He0.
  apply subst_only_matters_up_to_env.
  intros.
  destruct x; inversion H; subst; auto.
  simpl.

  revert H1.
  clear.
  revert Γ.
  induction x; intros. {
    destruct Γ; inversion H1; subst.
    simpl.
    reflexivity.
  } {
    erewrite dep_ids_ids; eauto.
  }
Qed.

Definition is_pure (e : u_expr) : Prop :=
  match e with
  | u_real _ | u_lam _ _ | u_var _ => True
  | _ => False
  end.

Lemma closed_pure_is_val {Γ τ} {e : expr Γ τ} :
  is_pure e ->
  forall ρ,
    is_val (proj1_sig (close ρ e)).
Proof.
  intros.

  elim_sig_exprs.
  destruct e;
    try contradiction H;
    cbn in He0;
    try elim_erase_eqs;
    auto.

  destruct (env_search_subst ρ H0) as [v Hv].
  elim_erase_eqs.

  destruct v.
  auto.
Qed.

Lemma beta_value {Γ τ τv}
      (e : expr (τv :: Γ) τ)
      (v : expr Γ τv) :
  is_pure v ->
  (EXP Γ ⊢ e_let v e ≈ proj1_sig (open_subst1 e v) : τ).
Proof.
  intro v_val.

  apply relate_exprs; intros.

  pose proof closed_pure_is_val v_val ρ.

  munge.
  rewrite <- H2 in H.
  set (v' := mk_val e1_2 H).
  replace e1_2 with (v' : expr _ _) in * by auto.
  clearbody v'.
  clear H.

  rewrite let_as_transformer.
  rewrite subst_val.

  munge.
  f_equal.

  apply erase_injective.
  rewrite He0, He2.
  asimpl.
  apply subst_only_matters_up_to_env.
  intros.

  destruct x; auto; cbn in *.
  erewrite dep_ids_ids; eauto.
Qed.

Lemma beta_value' {Γ τ τv}
      (e : expr (τv :: Γ) τ)
      (v : expr Γ τv) :
  is_pure v ->
  (EXP Γ ⊢ e_let v e ≈ proj1_sig (open_subst1 e v) : τ).
Proof.
  intros v_val.

  apply relate_exprs; intros.

  pose proof closed_pure_is_val v_val ρ.

  munge.
  rewrite <- H2 in H.
  set (v' := mk_val e1_2 H).
  replace e1_2 with (v' : expr _ _) in * by auto.
  clearbody v'.
  clear H.

  apply (coarsening (fun a b => μEntropy a = μEntropy b)); auto.
  intros.

  set (S1 := preimage _ _).
  set (S2 := preimage _ _).

  replace S1 with (preimage (π 2) S2); revgoals. {
    subst S1 S2.
    unfold preimage.
    extensionality σ.
    f_equal.
    unfold eval_in.
    decide_eval (e_let v' e1_1) σ as [vl wl El ul]. {
      dep_destruct El; try absurd_val.
      dep_destruct El1.
      apply invert_eval_val in El2.
      inject El2.
      munge.

      replace e0 with e2 in *; revgoals. {
        apply erase_injective.
        rewrite He2, He0.
        asimpl.
        apply subst_only_matters_up_to_env.
        intros.
        destruct x; cbn; auto.
        erewrite dep_ids_ids; eauto.
      }

      decide_eval as [vR wR ER uR]. {
        specialize (uR _ _ El3).
        inject uR.
        cbn.
        ring.
      }
    } {
      decide_eval as [vR wR ER uR].
      econtradict not_ex. {
        rewrite (rewrite_v_lam) in *.
        apply EVAL_val.
      } {
        munge.
        replace e0 with e2 in *; revgoals. {
          apply erase_injective.
          rewrite He2, He0.
          asimpl.
          apply subst_only_matters_up_to_env.
          intros.
          destruct x; cbn; auto.
          erewrite dep_ids_ids; eauto.
        }
        subst.
        eauto.
      }
    }
  } {
    clearbody S1 S2.
    subst.
    clear_except H.

    change ((μEntropy ∘ (preimage (π 2))) S2 = μEntropy S2).
    fold (pushforward μEntropy (π 2)).

    pose proof (fun f => project_same_integral f 2).
    setoid_rewrite integration_of_pushforward in H at 1.
    admit.
  }
Abort.

Lemma apply_id_equiv {Γ τ} (e : expr Γ τ) :
  (EXP Γ ⊢ e_let e var_0 ≈ e : τ).
Proof.
  intro He.
  apply relate_exprs; intros.

  munge.

  dep_destruct e0_1; try discriminate.
  inject H2.

  rewrite let_as_transformer.

  set (fun _ => _ >>= _).
  enough (m = dirac). {
    rewrite H0.
    rewrite meas_id_right.
    reflexivity.
  }
  subst m.
  clear e0_2 H1.

  extensionality v.
  munge.
  apply val_is_dirac.
Qed.

Lemma the_infinite_cons_doesnt_exist {A} {x : A} {xs} : (x :: xs <> xs).
Proof.
  intro.
  change ((x :: nil) ++ xs = nil ++ xs) in H.
  apply app_inv_tail in H.
  discriminate H.
Qed.

Definition simple_ctx_frame Γ τo τh := (FRAME Γ ⊢ [Γ ⊢ τh] : τo).
Definition simple_ctx Γ := chain (simple_ctx_frame Γ).

Lemma simple_ctx_frame_rect
      (P : forall Γ τo τi, simple_ctx_frame Γ τo τi -> Type)
      (case_app_f : forall Γ τa τr e,
          P Γ τr (τa ~> τr) (c_app_f e))
      (case_app_a : forall Γ τa τr e,
          P Γ τr τa (c_app_a e))
      (case_factor : forall Γ, P Γ ℝ ℝ c_factor)
      (case_plus_l : forall Γ e, P Γ ℝ ℝ (c_plus_l e))
      (case_plus_r : forall Γ e, P Γ ℝ ℝ (c_plus_r e))
      : forall Γ τo τi f, P Γ τo τi f.
Proof.
  intros.
  unfold simple_ctx_frame in *.
  dep_destruct f; auto.
  contradict (the_infinite_cons_doesnt_exist x0).
Qed.

Notation "'SIMPLE' Γ ⊢ [ τh ] : τo" := (simple_ctx Γ τo τh)
         (at level 70, Γ, τh, τo at level 200, no associativity).

Definition unsimple {Γ} : forall {τo τh},
    (SIMPLE Γ ⊢ [τh] : τo) -> (CTX Γ ⊢ [Γ ⊢ τh] : τo) :=
  fix unsimple {τo τh} S :=
    match S with
    | chain_nil => chain_nil
    | f ::: S' => f :::: unsimple S'
    end.

Lemma unsimple_cons {Γ τo τm τi}
      (p : simple_ctx_frame Γ τo τm)
      (S : SIMPLE Γ ⊢ [τi] : τm)
  : unsimple (p ::: S) = p :::: unsimple S.
Proof.
  trivial.
Qed.

Set Typeclasses Unique Instances.

Instance simple_plug Γ τo τh :
  Plug.Plug (SIMPLE Γ ⊢ [τh] : τo) (expr Γ τh) (expr Γ τo) :=
  { plug S e := (unsimple S)⟨e⟩ }.

Module Lift.
  Class type obj :=
    mk {
        lobj : Ty -> Type;
        lift1 τ0 : obj -> lobj τ0;
      }.
  Arguments mk {_ _} _.
End Lift.
Definition lift1 {o t} := @Lift.lift1 o t.

Notation "e ^ τ" := (lift1 τ e) (only printing).
(* The ltac:exact is needed to keep typeclasses from having trouble *)
Notation "e ^ τ" := ltac:(exact (lift1 τ e)) (only parsing).
Notation "e ↑" := (rename (+1) e) (at level 3).

Instance expr_lift Γ τ : Lift.type (expr Γ τ) :=
  Lift.mk (fun τ0 e => proj1_sig (expr_ren (+1) e (τ0 :: Γ) eq_refl)).

Lemma expr_lift_erase {Γ τ} (e : expr Γ τ) τ0 :
  erase (e ^ τ0) = (erase e)↑.
Proof.
  munge.
  rewrite He0.
  autosubst.
Qed.

Definition simple_ctx_frame_lift {Γ τo τe} τ0 (f : simple_ctx_frame Γ τo τe) :
  simple_ctx_frame (τ0 :: Γ) τo τe :=
  match f in (FRAME Γ' ⊢ [Γ'' ⊢ τe'] : τo')
        return (Γ'' = Γ' -> simple_ctx_frame (τ0 :: Γ') τo' τe')
  with
  | c_app_f e => fun _ => c_app_f (e ^ τ0)
  | c_app_a e => fun _ => c_app_a (e ^ τ0)
  | c_factor => fun _ => c_factor
  | c_plus_l e => fun _ => c_plus_l (e ^ τ0)
  | c_plus_r e => fun _ => c_plus_r (e ^ τ0)
  | c_lam => fun H => False_rect _ (the_infinite_cons_doesnt_exist H)
  end eq_refl.

Arguments simple_ctx_frame_lift _ _ _ _ !f.

Instance simple_ctx_frame_lift' Γ τo τe : Lift.type (simple_ctx_frame Γ τo τe) :=
  { lift1 := simple_ctx_frame_lift}.

Fixpoint up_simple_ctx' {Γ τe τo} τ0
         (S : (SIMPLE Γ ⊢ [τe] : τo))
  : (SIMPLE τ0 :: Γ ⊢ [τe] : τo) :=
  match S with
  | chain_nil => chain_nil
  | f ::: S' =>
    (f ^ τ0 : simple_ctx_frame _ _ _) ::: up_simple_ctx' τ0 S'
  end.

Instance up_simple_ctx Γ τe τo : Lift.type (SIMPLE Γ ⊢ [τe] : τo) :=
  Lift.mk up_simple_ctx'.

Lemma single_frame_case_app_f {Γ τe τa τo}
      (ea : expr Γ τa)
      (f_body : expr (τe :: Γ) (τa ~> τo))
      (e : expr Γ τe) :
  let S1 := (c_app_f (τr := τo) ea) in
  (EXP Γ ⊢ e_let e (S1^τe)⟨((λ, f_body)^τe) @ var_0⟩ ≈ S1⟨e_let e f_body⟩ : τo).
Proof.
  apply relate_exprs.
  intros.
  munge.

  rewrite apply_as_transformer.
  rewrite !let_as_transformer.

  rewrite meas_bind_assoc.
  integrand_extensionality va.
  munge.

  rewrite !apply_as_transformer.
  rewrite let_as_transformer.
  munge.

  asimpl in He1.
  asimpl in He0.
  asimpl in H2.

  elim_erase_eqs.
  reflexivity.
Qed.

Lemma single_frame_case_app_a {Γ τe τa τo}
      (ef : expr Γ (τa ~> τo))
      (f_body : expr (τe :: Γ) τa)
      (e : expr Γ τe) :
  let S1 := c_app_a ef in
  (EXP Γ ⊢ e_let e (S1^τe)⟨((λ, f_body)^τe) @ var_0⟩ ≈ S1⟨e_let e f_body⟩ : τo).
Proof.
  apply relate_exprs.
  intros.
  munge.

  rewrite !apply_as_transformer.
  rewrite !let_as_transformer.

  setoid_rewrite meas_bind_assoc.
  rewrite (μ_interchangable e3_1).
  integrand_extensionality va.
  munge.

  rewrite !apply_as_transformer.
  rewrite !let_as_transformer.
  munge.

  asimpl in He0.
  asimpl in He1.
  asimpl in H1.

  elim_erase_eqs.
  reflexivity.
Qed.

Lemma single_frame_case_factor {Γ τe}
      (f_body : expr (τe :: Γ) ℝ)
      (e : expr Γ τe) :
  let S1 := c_factor in
  (EXP Γ ⊢ e_let e (S1^τe)⟨((λ, f_body)^τe) @ var_0⟩ ≈ S1⟨e_let e f_body⟩ : ℝ).
Proof.
  apply relate_exprs.
  intros.
  munge.

  rewrite factor_as_transformer.
  rewrite !let_as_transformer.
  munge.

  rewrite meas_bind_assoc.
  integrand_extensionality va.
  munge.

  rewrite factor_as_transformer.
  rewrite !let_as_transformer.
  munge.

  asimpl in He0.
  asimpl in He1.
  elim_erase_eqs.

  reflexivity.
Qed.

Lemma single_frame_case_plus_l {Γ τe}
      (er : expr Γ ℝ)
      (f_body : expr (τe :: Γ) ℝ)
      (e : expr Γ τe) :
  let S1 := c_plus_l er in
  (EXP Γ ⊢ e_let e (S1^τe)⟨((λ, f_body)^τe) @ var_0⟩ ≈ S1⟨e_let e f_body⟩ : ℝ).
Proof.
  apply relate_exprs.
  intros.
  munge.

  rewrite plus_as_transformer.
  rewrite !let_as_transformer.
  munge.

  rewrite meas_bind_assoc.
  integrand_extensionality va.
  munge.

  rewrite plus_as_transformer.
  rewrite !let_as_transformer.
  munge.

  asimpl in He0.
  asimpl in He1.
  asimpl in H2.
  elim_erase_eqs.

  reflexivity.
Qed.

Lemma single_frame_case_plus_r {Γ τe}
      (el : expr Γ ℝ)
      (f_body : expr (τe :: Γ) ℝ)
      (e : expr Γ τe) :
  let S1 := c_plus_r el in
  (EXP Γ ⊢ e_let e (S1^τe)⟨((λ, f_body)^τe) @ var_0⟩ ≈ S1⟨e_let e f_body⟩ : ℝ).
Proof.
  apply relate_exprs.
  intros.
  munge.

  rewrite plus_as_transformer.
  rewrite !let_as_transformer.

  setoid_rewrite meas_bind_assoc.
  rewrite (μ_interchangable e3_1); auto.
  integrand_extensionality va.
  munge.

  rewrite plus_as_transformer.
  rewrite !let_as_transformer.
  munge.

  asimpl in He0.
  asimpl in He1.
  asimpl in H0.
  elim_erase_eqs.

  reflexivity.
Qed.

Lemma erase_plug {Γo Γi τi τo} (C : (CTX Γo ⊢ [Γi ⊢ τi] : τo)) e :
  erase C⟨e⟩ = (erase_ctx C)⟨erase e⟩.
Proof.
  induction C using bichain_rect; auto.

  rewrite plug_cons, erase_cons.
  change (erase x⟨C⟨e⟩⟩ = (erase_ctx_frame x)⟨(erase_ctx C)⟨erase e⟩⟩).
  rewrite <- IHC.
  destruct x; reflexivity.
Qed.

Definition erase_simple_ctx {Γ τi τo} (S : (SIMPLE Γ ⊢ [τi] : τo)) : u_ctx :=
  erase_ctx (unsimple S).

Lemma erase_simple_plug {Γ τi τo} (S : (SIMPLE Γ ⊢ [τi] : τo)) e :
  erase S⟨e⟩ = (erase_simple_ctx S)⟨erase e⟩.
Proof.
  apply erase_plug.
Qed.

Lemma erase_up_simple_ctx {Γ τo τi} (S : SIMPLE Γ ⊢ [τi] : τo) :
  erase_ctx (unsimple (S^τi)) = (erase_ctx (unsimple S))↑.
Proof.
  induction S; auto.
  cbn -[unsimple].
  rewrite !unsimple_cons, !erase_cons.
  cbn -[unsimple].
  f_equal; auto.

  destruct p using simple_ctx_frame_rect;
    cbn;
    auto;
    elim_sig_exprs;
    rewrite He0;
    rewrite rename_subst;
    auto.
Qed.

Fixpoint is_u_simple (u : u_ctx) : Prop :=
  match u with
  | nil => True
  | uc_lam _ :: _ => False
  | _ :: u' => is_u_simple u'
  end.

Lemma rename_simple_u_plug (U : u_ctx) (u : u_expr) σ :
  is_u_simple U ->
  rename σ U⟨u⟩ = (rename σ U)⟨rename σ u⟩.
Proof.
  intro U_simp.
  induction U; auto.
  unfold Plug.plug at 2 in IHU.
  destruct a;
    cbn in *;
    try contradiction U_simp;
    rewrite <- IHU;
    auto.
Qed.

Lemma plug_app {Γ τo τm τi}
      (Co : (SIMPLE Γ ⊢ [τm] : τo))
      (Ci : (SIMPLE Γ ⊢ [τi] : τm))
      (e : expr Γ τi)
  : Co⟨Ci⟨e⟩⟩ = (Co +++ Ci)⟨e⟩.
Proof.
  induction Co; auto.
  change (p⟨Co⟨Ci⟨e⟩⟩⟩ = p⟨(Co +++ Ci)⟨e⟩⟩).
  rewrite IHCo.
  reflexivity.
Qed.

Lemma up_cons {Γ τi τm τo}
      (f : simple_ctx_frame Γ τo τm)
      (S : (SIMPLE Γ ⊢ [τi] : τm))
      τ0 :
  (f ::: S)^τ0 = (f^τ0) ::: (S^τ0).
Proof.
  auto.
Qed.

Lemma up_app {Γ τi τm τo}
      (Co : (SIMPLE Γ ⊢ [τm] : τo))
      (Ci : (SIMPLE Γ ⊢ [τi] : τm))
      τ0 :
  (Co +++ Ci)^τ0 = (Co^τ0) +++ (Ci^τ0).
Proof.
  cbn.
  induction Co. {
    cbn.
    auto.
  } {
    specialize (IHCo Ci).
    cbn [chain_app up_simple_ctx' eq_rect].
    rewrite IHCo.
    auto.
  }
Qed.

Lemma simple_cons_plug {Γ τi τm τo}
      (f : simple_ctx_frame Γ τo τm)
      (S : (SIMPLE Γ ⊢ [τi] : τm))
      (e : expr Γ τi) :
  (f ::: S)⟨e⟩ = f⟨S⟨e⟩⟩.
Proof.
  trivial.
Qed.

Lemma erase_simple {Γ τo τi}
      (S : SIMPLE Γ ⊢ [τo] : τi)
  : is_u_simple (erase_ctx (unsimple S)).
Proof.
  induction S. {
    cbn.
    trivial.
  } {
    change (is_u_simple (erase_ctx (p :::: unsimple S))).
    rewrite erase_cons.
    destruct p using simple_ctx_frame_rect; auto.
  }
Qed.


Lemma pred_up {Γ τi τo} (S : SIMPLE Γ ⊢ [τi] : τo) (τu : Ty) :
  rename pred (erase_simple_ctx (S ^ τu)) = erase_simple_ctx S.
Proof.
  assert (ren ((+1) >>> pred) = ids) by auto.
  assert (forall e : u_expr, rename pred e↑ = e). {
    intros.
    asimpl.
    rewrite H.
    autosubst.
  }

  induction S; auto.
  rewrite (up_cons p S).
  unfold erase_simple_ctx.
  cbn [unsimple].
  rewrite !erase_cons.
  cbn -[lift1].
  f_equal; auto.

  clear IHS.

  dependent destruction p using simple_ctx_frame_rect;
    simpl;
    try elim_sig_exprs;
    rewrite ?He1, ?He0, ?H;
    f_equal;
    asimpl;
    rewrite ?H;
    autosubst.
Qed.

Ltac show_refl :=
  let H := fresh "H" in
  match goal with
  | [ |- EXP _ ⊢ ?a ≈ ?b : _ ] => enough (H : a = b) by (rewrite H; reflexivity)
  end.

(* Lemma single_frame_case_let {Γ τe τa τo} *)
(*       (ea : expr Γ τa) *)
(*       (f_body : expr (τe :: Γ) (τa ~> τo)) *)
(*       (e : expr Γ τe) : *)
(*   let S1 := (c_app_f (τr := τo) ea) :::: (c_lam : (FRAME Γ ⊢ [τe :: Γ ⊢ _] : _)) in *)
(*   (EXP Γ ⊢ e_let e (S1^τe)⟨((λ, f_body)^τe) @ var_0⟩ ≈ S1⟨e_let e f_body⟩ : τo). *)


(* theorem 24 *)
Theorem subst_into_simple {Γ τe τo}
        (S : SIMPLE Γ ⊢ [τe] : τo)
        (e : expr Γ τe) :
  (EXP Γ ⊢ e_let e ((S^τe)⟨var_0⟩) ≈ S⟨e⟩ : τo).
Proof.
  induction S. {
    cbn.
    apply apply_id_equiv.
  } {
    change (simple_ctx Γ B C) in S.
    rename A into τo, B into τm, C into τi.

    specialize (IHS e).
    change (EXP Γ ⊢ e_let e (p ^ τi)⟨(S ^ τi)⟨var_0⟩⟩ ≈ p⟨S⟨e⟩⟩ : τo).

    transitivity (e_let e ((p^τi)⟨e_let var_0 (((S^τi)^τi)⟨var_0⟩)⟩)). {
      (* "by theorem 22" *)
      apply compat_let; try reflexivity.

      apply compat_plug1.
      clear p.

      pose proof beta_value (((S^τi)^τi)⟨var_0⟩) var_0 I.
      etransitivity; revgoals.
      symmetry in H.
      apply H.

      show_refl.

      elim_sig_exprs.
      elim_erase_eqs.

      apply erase_injective.
      rewrite He0.
      clear.

      replace (u_var 0 .: ids) with (ren pred); swap 1 2. {
        extensionality n.
        destruct n; auto.
      }
      rewrite <- rename_subst.

      cbn.
      setoid_rewrite erase_plug.
      rewrite rename_simple_u_plug; [| apply erase_simple].
      setoid_rewrite pred_up.
      reflexivity.
    }

    transitivity (p⟨e_let e (S^τi)⟨var_0⟩⟩). {
      (* "by single-frame case" *)

      unfold e_let.

      set (f := λ, (S^τi)⟨var_0⟩).
      replace (λ, ((S^τi)^τi)⟨var_0⟩) with (f^τi); swap 1 2. {
        clear.
        subst f.
        simpl.

        elim_sig_exprs.
        elim_erase_eqs.
        f_equal.

        apply erase_injective.
        setoid_rewrite erase_plug.
        cbn.
        rewrite H0.
        clear e H0.
        setoid_rewrite erase_plug.
        rewrite <- rename_subst.

        rewrite rename_simple_u_plug; revgoals. {
          apply erase_simple.
        }
        f_equal.
        repeat setoid_rewrite erase_up_simple_ctx.

        generalize (erase_ctx (unsimple S)); intros.
        clear.

        assert (forall e : u_expr, rename (0 .: (+2)) (e↑) = e↑↑)
          by (intros; autosubst).

        induction u; auto.
        cbn.
        rewrite IHu.
        clear IHu.

        f_equal.
        destruct a; cbn; rewrite ?H; auto.
      }

      subst f.

      fold (e_let e (S ^ τi)⟨var_0⟩).
      fold (e_let e (p ^ τi)⟨(λ, (S ^ τi)⟨var_0⟩) ^ τi @ var_0⟩).

      dependent destruction p using simple_ctx_frame_rect.
      - apply single_frame_case_app_f.
      - apply single_frame_case_app_a.
      - apply single_frame_case_factor.
      - apply single_frame_case_plus_l.
      - apply single_frame_case_plus_r.
    }

    apply compat_plug1.
    exact IHS.
  }
Qed.

Print Assumptions subst_into_simple.

Definition var_swap : nat -> nat :=
  (fun x =>
    match x with
    | 0 => 1
    | 1 => 0
    | _ => x
    end)%nat.

Definition ty_swap {Γ τ1 τ2 τ} (e : expr (τ1 :: τ2 :: Γ) τ) :
  expr (τ2 :: τ1 :: Γ) τ.
Proof.
  refine (proj1_sig (expr_ren var_swap e (τ2 :: τ1 :: Γ) _)).
  abstract (extensionality x; do 2 (destruct x; auto)).
Defined.

Lemma let2_as_transformer {τ0 τ1 τr} (e0 : expr · τ0) (e1 : expr · τ1)
      (b : expr (τ1 :: τ0 :: ·) τr) :
  μ (e_let e0 (e_let (e1^τ0) b)) =
  μ e0 >>=
    (fun v0 =>
       μ e1 >>=
         (fun v1 =>
            μ (proj1_sig (close (dep_cons v1 (dep_cons v0 dep_nil)) b)))).
Proof.
  extensionality A.
  rewrite let_as_transformer.
  integrand_extensionality v0.
  munge.

  asimpl in H1.
  elim_erase_eqs.
  rewrite let_as_transformer.

  integrand_extensionality v1.
  munge.
  asimpl in He.
  elim_erase_eqs.
  reflexivity.
Qed.

Lemma is_commutative {Γ τ1 τ2 τ}
      (e1 : expr Γ τ1)
      (e2 : expr Γ τ2)
      (body : expr (τ2 :: τ1 :: Γ) τ) :
  (EXP Γ ⊢ e_let e1 (e_let (e2^τ1) body) ≈ e_let e2 (e_let (e1^τ2) (ty_swap body)) : τ).
Proof.
  apply relate_exprs.
  intros.
  unfold ty_swap.
  munge.

  replace e3_4 with (proj1_sig (close ρ e2) ^ τ1); revgoals. {
    elim_sig_exprs.
    elim_erase_eqs.
    asimpl in H4.
    asimpl in He0.
    elim_erase_eqs.
    reflexivity.
  }
  replace e3_1_2 with (proj1_sig (close ρ e1) ^ τ2); revgoals. {
    elim_sig_exprs.
    elim_erase_eqs.
    asimpl in H2.
    asimpl in He0.
    elim_erase_eqs.
    reflexivity.
  }

  rewrite 2 let2_as_transformer.
  rewrite μ_interchangable.
  munge.
  integrand_extensionality v2.
  integrand_extensionality v1.

  munge.
  asimpl in He3.
  asimpl in He4.
  f_equal.

  apply erase_injective.
  rewrite He3, He4.
  apply subst_only_matters_up_to_env.
  intros.
  repeat (destruct x; auto).
Qed.

Definition e_seq {Γ τ0 τ1} (e0 : expr Γ τ0) (e1 : expr Γ τ1) : expr Γ τ1 :=
  ((λ, (λ, var_0)) @ e0 @ e1).