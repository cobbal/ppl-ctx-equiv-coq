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
Require Import relations.
Require Import ctxequiv.
Require Import properties_of_relations.
Require Import integration.

Require Import micromega.Lia.

Local Open Scope nat.

Transparent π.

Notation "'λ,' e" := (e_lam e) (at level 69, right associativity).
Notation "e0 @ e1" := (e_app e0 e1) (at level 68, left associativity).
Notation "e0 +! e1" := (e_plus e0 e1).

Definition e_let {Γ τ0 τ1} (e0 : expr Γ τ0) (e1 : expr (τ0 :: Γ) τ1) := (λ, e1) @ e0.

Check apply_in.
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

Lemma add_zero_related (e : expr · ℝ) :
  (EXP · ⊢ e_real 0 +! e ≈ e : ℝ).
Proof.
  apply relate_exprs; intros.

  elim_sig_exprs.
  elim_erase_eqs.

  rewrite plus_as_transformer.
  setoid_rewrite (val_is_dirac (v_real 0)).
  rewrite meas_id_left.

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

  elim_sig_exprs.
  elim_erase_eqs.

  rewrite 2 plus_as_transformer.
  rewrite μ_interchangable.
  integrand_extensionality v1.
  integrand_extensionality v0.

  destruct_val v0.
  destruct_val v1.
  cbn.
  rewrite Rplus_comm.
  auto.
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

Lemma lam_is_dirac {τa τr} (e : expr (τa :: ·) τr) : μ (λ, e) = dirac (v_lam e).
Proof.
  rewrite <- val_is_dirac.
  reflexivity.
Qed.

Lemma beta_value {Γ τ τv}
      (e : expr (τv :: Γ) τ)
      (v : expr Γ τv) :
  is_pure v ->
  (EXP Γ ⊢ e_let v e ≈ proj1_sig (open_subst1 e v) : τ).
Proof.
  intros v_val.

  apply relate_exprs; intros.

  pose proof closed_pure_is_val v_val ρ.

  elim_sig_exprs.
  elim_erase_eqs.

  rewrite apply_as_transformer.
  rewrite lam_is_dirac.
  rewrite meas_id_left.
  cbn.
  rewrite <- H2 in H.

  setoid_rewrite (val_is_dirac (mk_val _ H)).
  rewrite meas_id_left.

  elim_sig_exprs.
  elim_erase_eqs.

  enough (e0 = e2) by (subst; auto).
  apply erase_injective.
  rewrite He2, He0.
  asimpl.
  apply subst_only_matters_up_to_env.
  intros.

  destruct x; auto; simpl in *.
  erewrite dep_ids_ids; eauto.
Qed.

Print Assumptions beta_value.

Lemma apply_id_equiv {Γ τ} (e : expr Γ τ) :
  (EXP Γ ⊢ e_let e var_0 ≈ e : τ).
Proof.
  intro He.
  apply relate_exprs; intros.

  elim_sig_exprs.
  elim_erase_eqs.

  dep_destruct e0_1; try discriminate.
  inject H2.

  rewrite apply_as_transformer.
  rewrite lam_is_dirac.
  rewrite meas_id_left.

  set (fun _ => _ >>= _).
  enough (m = dirac). {
    rewrite H0.
    rewrite meas_id_right.
    auto.
  }
  subst m.
  clear e0_2 H1.

  extensionality v.
  cbn.
  fold_μ.

  elim_sig_exprs.
  elim_erase_eqs.

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
  simpl.
  elim_sig_exprs.
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
  (EXP Γ ⊢ e_let e (S1^τe)⟨e_let var_0 (f_body^τe)⟩ ≈ S1⟨e_let e f_body⟩ : τo).
Proof.
  apply relate_exprs.
  intros.

  elim_sig_exprs.
  elim_erase_eqs.

  rewrite !apply_as_transformer.
  rewrite !lam_is_dirac.
  rewrite !meas_id_left.

  rewrite meas_bind_assoc.
  integrand_extensionality va.

  cbn.
  repeat fold_μ.
  elim_sig_exprs.
  elim_erase_eqs.

  repeat fold_μ.
  rewrite !apply_as_transformer.
  rewrite lam_is_dirac, val_is_dirac.
  rewrite !meas_id_left.
  cbn.

  elim_sig_exprs.
  elim_erase_eqs.
  fold_μ.

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
  (EXP Γ ⊢ e_let e (S1^τe)⟨e_let var_0 (f_body^τe)⟩ ≈ S1⟨e_let e f_body⟩ : τo).
Proof.
  apply relate_exprs.
  intros.

  elim_sig_exprs.
  elim_erase_eqs.

  rewrite !apply_as_transformer.
  rewrite !lam_is_dirac.
  rewrite !meas_id_left.

  setoid_rewrite meas_bind_assoc.
  rewrite (μ_interchangable e3_1).
  integrand_extensionality va.

  cbn.
  elim_sig_exprs.
  elim_erase_eqs.
  repeat fold_μ.

  rewrite !apply_as_transformer.
  rewrite lam_is_dirac.
  rewrite val_is_dirac.
  rewrite !meas_id_left.

  cbn.
  elim_sig_exprs.
  elim_erase_eqs.
  fold_μ.

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
  (EXP Γ ⊢ e_let e (S1^τe)⟨e_let var_0 (f_body^τe)⟩ ≈ S1⟨e_let e f_body⟩ : ℝ).
Proof.
  apply relate_exprs.
  intros.

  elim_sig_exprs.
  elim_erase_eqs.

  rewrite factor_as_transformer.
  rewrite !apply_as_transformer.
  rewrite !lam_is_dirac.
  rewrite !meas_id_left.

  rewrite meas_bind_assoc.
  integrand_extensionality va.

  cbn.
  elim_sig_exprs.
  elim_erase_eqs.
  repeat fold_μ.

  rewrite factor_as_transformer.
  rewrite !apply_as_transformer.
  rewrite lam_is_dirac.
  rewrite val_is_dirac.
  rewrite !meas_id_left.

  cbn.
  elim_sig_exprs.
  elim_erase_eqs.
  fold_μ.

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
  (EXP Γ ⊢ e_let e (S1^τe)⟨e_let var_0 (f_body^τe)⟩ ≈ S1⟨e_let e f_body⟩ : ℝ).
Proof.
  apply relate_exprs.
  intros.

  elim_sig_exprs.
  elim_erase_eqs.

  rewrite plus_as_transformer.
  rewrite !apply_as_transformer.
  rewrite !lam_is_dirac.
  rewrite !meas_id_left.

  rewrite meas_bind_assoc.
  integrand_extensionality va.

  cbn.
  elim_sig_exprs.
  elim_erase_eqs.
  repeat fold_μ.

  rewrite plus_as_transformer.
  rewrite !apply_as_transformer.
  rewrite lam_is_dirac.
  rewrite val_is_dirac.
  rewrite !meas_id_left.

  cbn.
  elim_sig_exprs.
  elim_erase_eqs.
  fold_μ.

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
  (EXP Γ ⊢ e_let e (S1^τe)⟨e_let var_0 (f_body^τe)⟩ ≈ S1⟨e_let e f_body⟩ : ℝ).
Proof.
  apply relate_exprs; intros.

  elim_sig_exprs.
  elim_erase_eqs.

  rewrite plus_as_transformer.
  rewrite !apply_as_transformer.
  rewrite !lam_is_dirac.
  rewrite !meas_id_left.

  setoid_rewrite meas_bind_assoc.
  rewrite (μ_interchangable e3_1); auto.
  integrand_extensionality va.

  cbn.
  elim_sig_exprs.
  elim_erase_eqs.
  repeat fold_μ.

  rewrite plus_as_transformer.
  rewrite !apply_as_transformer.
  rewrite lam_is_dirac.
  rewrite val_is_dirac.
  rewrite !meas_id_left.

  cbn.
  elim_sig_exprs.
  elim_erase_eqs.
  fold_μ.

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




      set (f := λ, (S^τi)⟨var_0⟩).
      unfold e_let at 2.
      replace (λ, ((S^τi)^τi)⟨var_0⟩) with (f^τi); swap 1 2. {
        admit.
      }
      subst f.
      cbn.
      unfold e_let in e0.

      dependent destruction p using simple_ctx_frame_rect.
      - apply single_frame_case_app_f.
      - apply single_frame_case_app_a.
      - apply single_frame_case_factor.
      - apply single_frame_case_plus_l.
      - apply single_frame_case_plus_r.








      replace (((S ^ τi) ^ τi)⟨var_0⟩) with (((S ^ τi)⟨var_0⟩ ^ τi)); revgoals. {

        assert (τm = τi) by admit.
        subst.
        assert (S = chain_nil) by admit.
        subst.
        cbn.
        simpl.

        destruct expr_ren.
        cbn.
        cbn in *.

        elim_sig_exprs.
        apply erase_injective.
        rewrite He0.
        clear e0 He0.
        setoid_rewrite erase_plug.
        rewrite <- rename_subst.

        rewrite rename_simple_u_plug by apply erase_simple.
        cbn.

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