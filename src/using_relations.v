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

Definition var_0 {τ Γ} : expr (τ :: Γ) τ :=
  e_var O (eq_refl : lookup (τ :: Γ) O = Some τ).

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
  apply relate_exprs.
  intros.

  elim_sig_exprs.
  elim_erase_eqs.

  rewrite by_μe_eq_μEntropy_plus.
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
  apply relate_exprs.
  intros.

  elim_sig_exprs.
  elim_erase_eqs.

  rewrite 2 by_μe_eq_μEntropy_plus.
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

Lemma lam_is_dirac {τa τr} (e : expr (τa :: ·) τr) : μ (λ, e) = dirac (v_lam e).
Proof.
  rewrite <- val_is_dirac.
  reflexivity.
Qed.

Lemma beta_value {Γ τ τv}
      (e : expr (τv :: Γ) τ)
      (v : expr Γ τv) :
  is_pure v ->
  (EXP Γ ⊢ (λ, e) @ v ≈ proj1_sig (open_subst1 e v) : τ).
Proof.
  intros v_val.

  apply relate_exprs.
  intros.

  elim_sig_exprs.
  elim_erase_eqs.

  rewrite by_μe_eq_μEntropy_app.
  rewrite lam_is_dirac.
  rewrite meas_id_left.
  cbn.

  assert (is_val e0_2). {
    revert H1 v_val; clear; intros.

    destruct v;
      try contradiction v_val;
      try solve [destruct e0_2; try discriminate; auto].

    destruct (env_search_subst ρ H) as [v Hv].
    cbn in *.
    elim_erase_eqs.

    destruct v.
    auto.
  }

  setoid_rewrite (val_is_dirac (mk_val _ H)).
  rewrite meas_id_left.

  elim_sig_exprs.
  elim_erase_eqs.

  enough (e0 = e1) by (subst; auto).
  apply erase_injective.
  rewrite He1, He0.
  asimpl.
  apply subst_only_matters_up_to_env.
  intros.

  destruct x; auto; simpl in *.
  erewrite dep_ids_ids; eauto.
Qed.

Print Assumptions beta_value.

Lemma apply_id_equiv {Γ τ} (e : expr Γ τ) :
  (EXP Γ ⊢ (λ, var_0) @ e ≈ e : τ).
Proof.
  intro He.

  apply relate_exprs.
  intros.

  elim_sig_exprs.
  elim_erase_eqs.

  rewrite by_μe_eq_μEntropy_app.
  rewrite lam_is_dirac.
  rewrite meas_id_left.

  set (fun _ => _ >>= _).
  enough (m = dirac). {
    rewrite H.
    rewrite meas_id_right.
    auto.
  }
  subst m.

  extensionality v.
  cbn.
  fold_μ.

  elim_sig_exprs.
  elim_erase_eqs.

  asimpl in He0.
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
  Plug.type (SIMPLE Γ ⊢ [τh] : τo) (expr Γ τh) (expr Γ τo) :=
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

(* Notation "e ^ τ" := (lift1 τ e). *)
Notation "e ^ τ" := (lift1 τ e) (only printing).
(* temporary brute force way to make the typeclass resolution be less searchy
   and more find the obvious instancy. *)
Notation "e ^ τ" := ltac:(exact (lift1 τ e)) (only parsing).
Notation "e ↑" := (rename (+1) e) (at level 3).

(* Instance ren_lift {A} {r : Rename A} : Liftable (const A) := *)
(*   { lift1 Γ τ e := rename (+1) (e : A) }. *)

(* Lemma ctx_rename_compose (S : Ctx) (f g : nat -> nat) : *)
(*   rename f (rename g S) = rename (f ∘ g) S. *)
(* Proof. *)
(*   unfold rename. *)
(*   revert f g. *)
(*   induction S; intros; simpl; rewrite ?IHS, ?H; auto; try autosubst. *)
(*   f_equal. *)
(*   assert (upren f ∘ upren g = upren (f ∘ g)). { *)
(*     compute. *)
(*     extensionality x. *)
(*     destruct x; auto. *)
(*   } *)
(*   rewrite <- H. *)
(*   auto. *)
(* Qed. *)

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

Lemma pure_of_val {τ} (v : val τ) : is_pure v.
Proof.
  destruct v using wt_val_rect; subst; simpl; trivial.
Qed.

Lemma single_frame_case_app_l {Γ τe τa τo}
      (ea : expr Γ τa)
      (f : expr Γ (τe ~> τa ~> τo))
      (e : expr Γ τe) :
  is_val f ->
  let S1 := (c_app_f (τr := τo) ea) in
  (EXP Γ ⊢ (λ, (S1^τe)⟨(f^τe) @ var_0⟩) @ e ≈ S1⟨f @ e⟩ : τo).
Proof.
  intros f_val.
  simpl.

  apply relate_exprs.
  intros.
  elim_sig_exprs.

  dep_destruct f; inversion_clear f_val.
  simpl in *.
  elim_erase_eqs.

  rewrite !by_μe_eq_μEntropy_app.
  rewrite !lam_is_dirac.
  rewrite !meas_id_left.

  rewrite meas_bind_assoc.
  integrand_extensionality va.

  cbn.
  elim_sig_exprs.
  elim_erase_eqs.

  repeat fold_μ.
  rewrite !by_μe_eq_μEntropy_app.
  rewrite lam_is_dirac, val_is_dirac.
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

Lemma single_frame_case_app_r {Γ τe τa τo}
      (ef : expr Γ (τa ~> τo))
      (f : expr Γ (τe ~> τa))
      (e : expr Γ τe) :
  is_val f ->
  let S1 := c_app_a ef in
  (EXP Γ ⊢ (λ, (S1^τe)⟨(f^τe) @ var_0⟩) @ e ≈ S1⟨f @ e⟩ : τo).
Proof.
  intros f_val.
  simpl.

  apply relate_exprs.
  intros.
  elim_sig_exprs.

  expr_destruct f; inversion_clear f_val.
  simpl in *.
  elim_erase_eqs.

  rewrite !by_μe_eq_μEntropy_app.
  rewrite !lam_is_dirac.
  rewrite !meas_id_left.

  setoid_rewrite meas_bind_assoc.
  rewrite (μ_interchangable e3_1).
  integrand_extensionality va.

  cbn.
  elim_sig_exprs.
  elim_erase_eqs.
  repeat fold_μ.

  rewrite !by_μe_eq_μEntropy_app.
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
      (f : expr Γ (τe ~> ℝ))
      (e : expr Γ τe) :
  is_val f ->
  let S1 := c_factor in
  (EXP Γ ⊢ (λ, (S1^τe)⟨(f^τe) @ var_0⟩) @ e ≈ S1⟨f @ e⟩ : ℝ).
Proof.
  intros f_val.
  simpl.

  apply relate_exprs.
  intros.
  elim_sig_exprs.

  expr_destruct f; inversion_clear f_val.
  simpl in *.
  elim_erase_eqs.

  rewrite by_μe_eq_μEntropy_factor.
  rewrite !by_μe_eq_μEntropy_app.
  rewrite !lam_is_dirac.
  rewrite !meas_id_left.

  rewrite meas_bind_assoc.
  integrand_extensionality va.

  cbn.
  elim_sig_exprs.
  elim_erase_eqs.
  repeat fold_μ.

  rewrite by_μe_eq_μEntropy_factor.
  rewrite !by_μe_eq_μEntropy_app.
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
      (f : expr Γ (τe ~> ℝ))
      (e : expr Γ τe) :
  is_val f ->
  let S1 := c_plus_l er in
  (EXP Γ ⊢ (λ, (S1^τe)⟨(f^τe) @ var_0⟩) @ e ≈ S1⟨f @ e⟩ : ℝ).
Proof.
  intros f_val.
  simpl.

  apply relate_exprs.
  intros.
  elim_sig_exprs.

  expr_destruct f; inversion_clear f_val.
  simpl in *.
  elim_erase_eqs.

  rewrite by_μe_eq_μEntropy_plus.
  rewrite !by_μe_eq_μEntropy_app.
  rewrite !lam_is_dirac.
  rewrite !meas_id_left.

  rewrite meas_bind_assoc.
  integrand_extensionality va.

  cbn.
  elim_sig_exprs.
  elim_erase_eqs.
  repeat fold_μ.

  rewrite by_μe_eq_μEntropy_plus.
  rewrite !by_μe_eq_μEntropy_app.
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
      (f : expr Γ (τe ~> ℝ))
      (e : expr Γ τe) :
  is_val f ->
  let S1 := c_plus_r el in
  (EXP Γ ⊢ (λ, (S1^τe)⟨(f^τe) @ var_0⟩) @ e ≈ S1⟨f @ e⟩ : ℝ).
Proof.
  intros f_val.
  simpl.

  apply relate_exprs.
  intros.
  elim_sig_exprs.

  expr_destruct f; inversion_clear f_val.
  simpl in *.
  elim_erase_eqs.

  rewrite by_μe_eq_μEntropy_plus.
  rewrite !by_μe_eq_μEntropy_app.
  rewrite !lam_is_dirac.
  rewrite !meas_id_left.

  setoid_rewrite meas_bind_assoc.
  rewrite (μ_interchangable e3_1); auto.
  integrand_extensionality va.

  cbn.
  elim_sig_exprs.
  elim_erase_eqs.
  repeat fold_μ.

  rewrite by_μe_eq_μEntropy_plus.
  rewrite !by_μe_eq_μEntropy_app.
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

Lemma rename_u_simple (U : u_ctx) σ :
  is_u_simple U -> is_u_simple (rename σ U).
Proof.
  intros.
  induction U; auto.
  destruct a; auto.
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
  auto.
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

(* theorem 24 *)
Theorem subst_into_simple {Γ τe τo}
        (S : SIMPLE Γ ⊢ [τe] : τo)
        (e : expr Γ τe) :
  (EXP Γ ⊢ (λ, (S^τe)⟨var_0⟩) @ e ≈ S⟨e⟩ : τo).
Proof.
  induction S. {
    cbn.
    apply apply_id_equiv.
  } {
    unfold simple_ctx_frame in p.
    change (simple_ctx Γ B C) in S.
    rename A into τo, B into τm, C into τi.
    transitivity ((λ, (p^τi)⟨(λ, ((S^τi)^τi)⟨var_0⟩) @ var_0⟩) @ e). {
      (* "by theorem 22" *)
      eapply compat_app; [| reflexivity].
      apply compat_lam.

      pose proof beta_value (((S^τi)^τi)⟨var_0⟩) var_0 I.

      setoid_rewrite up_cons.
      rewrite (simple_cons_plug (p^τi) (S^τi)).

      eapply compat_plug1.

      repeat destruct open_subst1; simpl in *.
      rewrite H.
      clear H.

      enough ((S^τi)⟨var_0⟩ = x) by (subst; reflexivity).
      apply erase_injective.
      rewrite e0.
      setoid_rewrite erase_plug.
      simpl.
      clear.

      replace (u_var 0 .: ids) with (ren pred); swap 1 2. {
        extensionality n.
        destruct n; auto.
      }
      rewrite <- rename_subst.

      rewrite rename_simple_u_plug; [| apply erase_simple]. {
        f_equal.

        change (erase_ctx (unsimple (S^τi)) =
                rename pred (erase_ctx (unsimple ((S^τi)^τi)))).

        assert (forall e : u_expr, rename pred e↑ = e). {
          intros.
          asimpl.
          replace (ren ((+1) >>> pred)) with ids by auto.
          autosubst.
        }

        induction S; auto.
        rewrite (up_cons p S).
        rewrite (up_cons (p^C) (S^C)).
        cbn [unsimple].
        rewrite !erase_cons.
        cbn -[lift1].
        dependent destruction p using simple_ctx_frame_rect;
          cbn;
          try elim_sig_exprs;
          rewrite ?He1, ?He0, ?H;
          f_equal;
          autosubst.
      }
    }

    transitivity (p⟨(λ, (S^τi)⟨var_0⟩) @ e⟩). {
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

      assert (is_val f) by exact I.
      clearbody f.

      change (simple_ctx_frame Γ τo τm) in p.
      dependent destruction p using simple_ctx_frame_rect.
      - apply single_frame_case_app_l; auto.
      - apply single_frame_case_app_r; auto.
      - apply single_frame_case_factor; auto.
      - apply single_frame_case_plus_l; auto.
      - apply single_frame_case_plus_r; auto.
    }

    cbn [Plug.plug simple_plug].
    rewrite unsimple_cons.
    rewrite plug_cons.

    apply compat_plug1.
    apply IHS.
  }
Qed.

Print Assumptions subst_into_simple.