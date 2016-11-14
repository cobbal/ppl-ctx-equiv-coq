Require Import Basics.
Require Import Reals.
Require Import List.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import nnr.
Require Import syntax.
Require Import utils.
Require Import Coq.Classes.Morphisms.
Require Import relations.
Require Import ctxequiv.
Require Import properties_of_relations.

Require Import micromega.Lia.

Transparent π.

Notation "x ~> y" := (Arrow x y) (at level 69, right associativity, y at level 70).
(* Notation "` x" := (e_var x) (at level 1). *)
Notation "'λ,' e" := (e_lam e) (at level 69, right associativity).
Notation "e0 @ e1" := (e_app e0 e1) (at level 68, left associativity).
Notation "e0 +! e1" := (e_plus e0 e1) (at level 68, left associativity).

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
  erewrite int_const_entropy; eauto.
Qed.

Lemma πR_same_integral f :
  integration (f ∘ πR) μEntropy = integration f μEntropy.
Proof.
  replace (f ∘ πR) with (fun σ => block (fun σL σR => f σR) (πL σ) (πR σ)) by auto.
  rewrite integration_πL_πR.
  unfold block.
  simpl.
  erewrite int_const_entropy; eauto.
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

(* A subset of things that can be tonellied *)
(* TODO: figure out exactly what's needed to make this not a whitelist *)
Inductive tonelliable : forall {A}, Meas A -> Type :=
| tonelliable_μ {τ} (e : expr · τ) : tonelliable (μ e)
| tonelliable_sig_fi {A} (m : Meas A) : SigmaFinite m -> tonelliable m
.
Hint Constructors tonelliable.

(* Lemma tonelli_μ {τ0 τ1 B} *)
(*       (e0 : expr · τ0) *)
(*       (e1 : expr · τ1) *)
(*       (f : val τ0 -> val τ1 -> Meas B) : *)
(*   μ e0 >>= (fun x => μ e1 >>= (fun y => f x y)) = *)
(*   μ e1 >>= (fun y => μ e0 >>= (fun x => f x y)). *)
(* Proof. *)
(* Abort. *)

Lemma tonelli_μ_and_finite {τ B C}
      (μFin : Meas B)
      (f : val τ -> B -> Meas C)
      (e : expr · τ) :
  SigmaFinite μFin ->
  μ e >>= (fun x => μFin >>= (fun y => f x y)) =
  μFin >>= (fun y => μ e >>= (fun x => f x y)).
Proof.
  intros.

  extensionality ev.

  rewrite μe_eq_μEntropy.
  setoid_rewrite μe_eq_μEntropy.
  setoid_rewrite tonelli_sigma_finite; auto.
  integrand_extensionality σ0.
  decide_eval as [v0 w0 ex0 u0]. {
    simpl.
    apply integration_linear_mult_r.
  } {
    simpl.
    rewrite <- integration_linear_mult_r.
    nnr.
  }
Qed.

Lemma tonelli
      {A B C} (μ0 : Meas A) (μ1 : Meas B)
      (f : A -> B -> Meas C) :
  tonelliable μ0 ->
  tonelliable μ1 ->
  μ0 >>= (fun x0 => μ1 >>= (fun x1 => f x0 x1)) =
  μ1 >>= (fun x1 => μ0 >>= (fun x0 => f x0 x1)).
Proof.
  intros.

  extensionality ev.
  d_destruct (X, X0). {
    rewrite !μe_eq_μEntropy2.
    setoid_rewrite tonelli_sigma_finite at 1; auto.
    integrand_extensionality σ0.
    integrand_extensionality σ1.

    decide_eval as [v0 w0 ex0 u0].
    decide_eval as [v1 w1 ex1 u1].
    simpl.
    nnr.
  } {
    rewrite tonelli_μ_and_finite; auto.
  } {
    rewrite tonelli_μ_and_finite; auto.
  } {
    apply tonelli_sigma_finite; auto.
  }
Qed.

Lemma add_comm_related Γ (e0 e1 : expr Γ ℝ) :
  (EXP Γ ⊢ e0 +! e1 ≈ e1 +! e0 : ℝ).
Proof.
  apply relate_exprs.
  intros.

  elim_sig_exprs.
  elim_erase_eqs.

  rewrite 2 by_μe_eq_μEntropy_plus.
  rewrite tonelli; auto.
  integrand_extensionality v1.
  integrand_extensionality v0.

  destruct_val v0.
  destruct_val v1.
  unfold plus_in; simpl.
  rewrite Rplus_comm.
  auto.
Qed.

Program Fixpoint dep_ids' (Γ0 Γ1 : Env Ty) : dep_env (expr (Γ0 ++ Γ1)) Γ1 :=
  match Γ1 return dep_env (expr (Γ0 ++ Γ1)) Γ1 with
  | nil => dep_nil
  | τ :: Γ1' =>
    dep_cons
      (e_var (length Γ0) _)
      (rew <- [fun z => dep_env (expr z) _] (app_assoc Γ0 (τ :: nil) Γ1') in
          dep_ids' (Γ0 ++ τ :: nil) Γ1')
  end.
Next Obligation.
  induction Γ0; auto.
Qed.

Definition dep_ids := dep_ids' ·.

Lemma erase_eq (Γ Γ0 Γ1 : Env Ty)
      (d0 : dep_env (expr Γ0) Γ)
      (d1 : dep_env (expr Γ1) Γ)
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
    d_destruct e.
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

  assert (is_val e0_2). {
    revert H1 v_val; clear; intros.
    destruct v;
      try contradiction v_val;
      try solve [destruct e0_2; try discriminate; auto].

    destruct (env_search ρ H) as [v Hv].
    pose proof lookup_subst ρ Hv.

    simpl in *.
    elim_erase_eqs.

    destruct v.
    auto.
  }

  setoid_rewrite (val_is_dirac (mk_val _ H)).
  rewrite meas_id_left.

  rewrite elim_apply_in.
  elim_sig_exprs.
  elim_erase_eqs.

  fold_μ.
  f_equal.
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
  rewrite elim_apply_in.
  elim_sig_exprs.
  fold (μ e0).

  elim_erase_eqs.
  asimpl in He0.
  elim_erase_eqs.

  apply val_is_dirac.
Qed.

Fixpoint is_simple {Γo Γi τi τo} (c : (CTX Γo ⊢ [Γi ⊢ τi] : τo)) : Prop :=
  match c with
  | c_hole => True

  | c_app_l c' _
  | c_app_r _ c'
  | c_factor c'
  | c_plus_l c' _
  | c_plus_r _ c' => is_simple c'

  | c_lam _ => False
  end.

Class Liftable (A : Env Ty -> Type) :=
  { lift1 {Γ} τ0 : A Γ -> A (τ0 :: Γ) }.

Notation "e ^ τ" := (lift1 τ e).
Notation "e ↑" := (rename (+1) e) (at level 3).

Instance ren_lift {A} {r : Rename A} : Liftable (const A) :=
  { lift1 Γ τ e := rename (+1) (e : A) }.

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

Instance expr_lift1 {τ} : Liftable (fun Γ => expr Γ τ) :=
  { lift1 Γ τ e :=
      proj1_sig (expr_ren (+1) e (τ :: Γ) eq_refl) }.

Lemma expr_lift1_erase {Γ τ} (e : expr Γ τ) τ0 :
  erase (e ^ τ0) = (erase e)↑.
Proof.
  simpl.
  elim_sig_exprs.
  rewrite He0.
  autosubst.
Qed.

Lemma up_simple_ctx {Γ τe τo} (S : (CTX Γ ⊢ [Γ ⊢ τe] : τo)) τ0 :
  is_simple S ->
  {S' : (CTX (τ0 :: Γ) ⊢ [(τ0 :: Γ) ⊢ τe] : τo) |
   is_simple S' /\
   erase_ctx S' = (erase_ctx S)↑ }.
Proof.
  intro S_simple.
  induction S;
    try contradiction S_simple;
    try destruct (IHS S_simple) as [S' [? HS']];
    try (pose (e ^ τ0) as e'';
         simpl in e'';
         destruct expr_ren as [e' He'] in e'';
         clear e''
        );
    [ (exists (c_hole))
    | (exists (c_app_l S' e'))
    | (exists (c_app_r e' S'))
    | (exists (c_factor S'))
    | (exists (c_plus_l S' e'))
    | (exists (c_plus_r e' S'))
    ];
    simpl;
    rewrite ?HS', ?He';
    auto.
Qed.

(* not to self: may want to make this say more than length later *)
Lemma contexts_dont_hide_variables {Γo Γi τo τi} (C : (CTX Γo ⊢ [Γi ⊢ τi] : τo)) :
  length Γo <= length Γi.
Proof.
  intros.
  dependent induction C; simpl; auto. {
    simpl in *.
    etransitivity; [| apply IHC].
    auto.
  }
Qed.

Lemma unchanged_env_means_simple {Γ τo τi} (S : (CTX Γ ⊢ [Γ ⊢ τi] : τo)) :
  is_simple S.
Proof.
  dependent induction S; try apply IHS; simpl; auto.
  pose proof contexts_dont_hide_variables S.

  contradict H.
  apply lt_not_le.
  auto.
Qed.

Instance ctx_lift {τi τo} : Liftable (fun Γ => (CTX Γ ⊢ [Γ ⊢ τi] : τo)) :=
  { lift1 Γ τ C :=
      proj1_sig (up_simple_ctx C τ (unchanged_env_means_simple C)) }.

(* TODO: figure out why type classes sometimes get stupidly confused if I don't
   explicitly instantiate them. *)
Notation "e ^^ τ" := (lift1 (Liftable := ctx_lift) τ e)
                       (at level 30, right associativity).

Lemma pure_of_val {τ} (v : val τ) : is_pure v.
Proof.
  destruct v using wt_val_rect; subst; simpl; trivial.
Qed.

Lemma single_frame_case_app_l {Γ τe τa τo}
      (ea : expr Γ τa)
      (f : expr Γ (τe ~> τa ~> τo))
      (e : expr Γ τe) :
  is_val f ->
  let S1 := (c_app_l (τr := τo) c_hole ea) in
  (EXP Γ ⊢ (λ, (S1^^τe)⟨(f^τe) @ var_0⟩) @ e ≈ S1⟨f @ e⟩ : τo).
Proof.
  intros f_val.
  simpl.

  apply relate_exprs.
  intros.
  destruct up_simple_ctx as [? [? ?]]; simpl.
  elim_sig_exprs.

  destruct x; inject e0.
  simpl in *.
  destruct x; inject H0.
  simpl in *.
  elim_erase_eqs.

  d_destruct f; inversion_clear f_val.
  simpl in *.
  elim_erase_eqs.

  rewrite !by_μe_eq_μEntropy_app.
  rewrite !lam_is_dirac.
  rewrite !meas_id_left.

  rewrite meas_bind_assoc.
  integrand_extensionality va.

  rewrite !elim_apply_in.
  elim_sig_exprs.
  elim_erase_eqs.

  repeat fold_μ.
  rewrite !by_μe_eq_μEntropy_app.
  rewrite lam_is_dirac.
  rewrite val_is_dirac.
  rewrite !meas_id_left.

  rewrite elim_apply_in.
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
  let S1 := (c_app_r ef c_hole) in
  (EXP Γ ⊢ (λ, (S1^^τe)⟨(f^τe) @ var_0⟩) @ e ≈ S1⟨f @ e⟩ : τo).
Proof.
  intros f_val.
  simpl.

  apply relate_exprs.
  intros.
  destruct up_simple_ctx as [? [? ?]]; simpl.
  elim_sig_exprs.

  destruct x; inject e0.
  destruct x; inversion_clear H1.

  expr_destruct f; inversion_clear f_val.
  simpl in *.
  elim_erase_eqs.

  rewrite !by_μe_eq_μEntropy_app.
  rewrite !lam_is_dirac.
  rewrite !meas_id_left.

  setoid_rewrite meas_bind_assoc.
  rewrite (tonelli (μ e3_1)); auto.
  integrand_extensionality va.

  rewrite !elim_apply_in.
  elim_sig_exprs.
  elim_erase_eqs.

  repeat fold_μ.
  rewrite !by_μe_eq_μEntropy_app.
  rewrite lam_is_dirac.
  rewrite val_is_dirac.
  rewrite !meas_id_left.

  rewrite elim_apply_in.
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
  let S1 := c_factor c_hole in
  (EXP Γ ⊢ (λ, (S1^^τe)⟨(f^τe) @ var_0⟩) @ e ≈ S1⟨f @ e⟩ : ℝ).
Proof.
  intros f_val.
  simpl.

  apply relate_exprs.
  intros.
  destruct up_simple_ctx as [? [? ?]]; simpl.
  elim_sig_exprs.

  destruct x; inject e0.
  d_destruct x; inversion_clear H0.

  expr_destruct f; inversion_clear f_val.
  simpl in *.
  elim_erase_eqs.

  rewrite by_μe_eq_μEntropy_factor.
  rewrite !by_μe_eq_μEntropy_app.
  rewrite !lam_is_dirac.
  rewrite !meas_id_left.

  rewrite meas_bind_assoc.
  integrand_extensionality va.

  rewrite !elim_apply_in.
  elim_sig_exprs.
  elim_erase_eqs.

  repeat fold_μ.
  rewrite by_μe_eq_μEntropy_factor.
  rewrite !by_μe_eq_μEntropy_app.
  rewrite lam_is_dirac.
  rewrite val_is_dirac.
  rewrite !meas_id_left.

  rewrite elim_apply_in.
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
  let S1 := (c_plus_l c_hole er) in
  (EXP Γ ⊢ (λ, (S1^^τe)⟨(f^τe) @ var_0⟩) @ e ≈ S1⟨f @ e⟩ : ℝ).
Proof.
  intros f_val.
  simpl.

  apply relate_exprs.
  intros.
  destruct up_simple_ctx as [? [? ?]]; simpl.
  elim_sig_exprs.

  destruct x; inject e0.
  d_destruct x; inversion_clear H0.

  expr_destruct f; inversion_clear f_val.
  simpl in *.
  elim_erase_eqs.

  rewrite by_μe_eq_μEntropy_plus.
  rewrite !by_μe_eq_μEntropy_app.
  rewrite !lam_is_dirac.
  rewrite !meas_id_left.

  rewrite meas_bind_assoc.
  integrand_extensionality va.

  rewrite !elim_apply_in.
  elim_sig_exprs.
  elim_erase_eqs.

  repeat fold_μ.
  rewrite by_μe_eq_μEntropy_plus.
  rewrite !by_μe_eq_μEntropy_app.
  rewrite lam_is_dirac.
  rewrite val_is_dirac.
  rewrite !meas_id_left.

  rewrite elim_apply_in.
  elim_sig_exprs.
  elim_erase_eqs.

  fold_μ.

  asimpl in He0.
  asimpl in He1.
  asimpl in H1.
  elim_erase_eqs.

  reflexivity.
Qed.

Lemma single_frame_case_plus_r {Γ τe}
      (el : expr Γ ℝ)
      (f : expr Γ (τe ~> ℝ))
      (e : expr Γ τe) :
  is_val f ->
  let S1 := (c_plus_r el c_hole) in
  (EXP Γ ⊢ (λ, (S1^^τe)⟨(f^τe) @ var_0⟩) @ e ≈ S1⟨f @ e⟩ : ℝ).
Proof.
  intros f_val.
  simpl.

  apply relate_exprs.
  intros.
  destruct up_simple_ctx as [? [? ?]]; simpl.
  elim_sig_exprs.

  destruct x; inject e0.
  d_destruct x; inversion_clear H1.

  expr_destruct f; inversion_clear f_val.
  simpl in *.
  elim_erase_eqs.

  rewrite by_μe_eq_μEntropy_plus.
  rewrite !by_μe_eq_μEntropy_app.
  rewrite !lam_is_dirac.
  rewrite !meas_id_left.

  setoid_rewrite meas_bind_assoc.
  rewrite (tonelli (μ e3_1)); auto.
  integrand_extensionality va.

  rewrite !elim_apply_in.
  elim_sig_exprs.
  elim_erase_eqs.

  repeat fold_μ.
  rewrite by_μe_eq_μEntropy_plus.
  rewrite !by_μe_eq_μEntropy_app.
  rewrite lam_is_dirac.
  rewrite val_is_dirac.
  rewrite !meas_id_left.

  rewrite elim_apply_in.
  elim_sig_exprs.
  elim_erase_eqs.

  fold_μ.

  asimpl in He0.
  asimpl in He1.
  asimpl in H0.
  elim_erase_eqs.

  reflexivity.
Qed.

(* Lemma rename_plugged_simple S σ e : *)
(*   is_simple S -> *)
(*   rename σ (S⟨e⟩) = (rename σ S)⟨rename σ e⟩. *)
(* Proof. *)
(*   intros. *)
(*   induction S; simpl; auto; fold rename; rewrite ?IHS; auto. *)
(*   contradiction H. *)
(* Qed. *)

Definition is_simple_single {Γ τi τo} (C : (CTX Γ ⊢ [Γ ⊢ τi] : τo)) : Prop :=
  match C with
  | c_app_l c_hole _
  | c_app_r _ c_hole
  | c_factor c_hole
  | c_plus_l c_hole _
  | c_plus_r _ c_hole
    => True
  | _ => False
  end.

Lemma single_is_simple {Γ τi τo} (C : (CTX Γ ⊢ [Γ ⊢ τi] : τo)) :
  is_simple_single C -> is_simple C.
Proof.
  intros.
  d_destruct C; simpl; auto; d_destruct C; tauto.
Qed.

Lemma simple_plug_simple {Γo Γm Γi τi τm τo}
      {So : (CTX Γo ⊢ [Γm ⊢ τm] : τo)}
      {Si : (CTX Γm ⊢ [Γi ⊢ τi] : τm)} :
  is_simple So ->
  is_simple Si ->
  is_simple (plug_ctx So Si).
Proof.
  intros.
  induction So; try contradiction H; auto.
Defined.

Lemma tc_ctx_single_rect {Γ}
      (P : forall τh τ (S : (CTX Γ ⊢ [Γ ⊢ τh] : τ)),
          is_simple S ->
          Type) :
  (forall τh, P τh τh c_hole I) ->
  (forall (τh τm τ : Ty)
          (S1 : CTX Γ ⊢ [Γ ⊢ τm] : τ)
          (S : CTX Γ ⊢ [Γ ⊢ τh] : τm)
          (S_simple : is_simple S)
          (S1_single : is_simple_single S1),
      P τh τm S S_simple ->
      P τh τ (plug_ctx S1 S)
        (simple_plug_simple (single_is_simple _ S1_single) S_simple)) ->
  forall τh τ S S_simple,
    P τh τ S S_simple.
Proof.
  intros case_hole case_composition.
  intros.
  dependent induction S;
    intros;
    try contradiction S_simple;
    try specialize (IHS case_hole case_composition).
  {
    destruct S_simple.
    apply case_hole.
  } {
    specialize (case_composition _ _ _ (c_app_l c_hole e) S).
    apply (case_composition S_simple I).
    apply IHS; auto.
  } {
    specialize (case_composition _ _ _ (c_app_r e c_hole) S).
    apply (case_composition S_simple I).
    apply IHS.
  } {
    specialize (case_composition _ _ _ (c_factor c_hole) S).
    apply (case_composition S_simple I).
    apply IHS.
  } {
    specialize (case_composition _ _ _ (c_plus_l c_hole e) S).
    apply (case_composition S_simple I).
    apply IHS.
  } {
    specialize (case_composition _ _ _ (c_plus_r e c_hole) S).
    apply (case_composition S_simple I).
    apply IHS.
  }
Qed.

(* Lemma rename_plug_ctx C C' σ : *)
(*   is_simple C -> *)
(*   rename σ (plug_ctx C C') = plug_ctx (rename σ C) (rename σ C'). *)
(* Proof. *)
(*   intros. *)
(*   induction C; intros; simpl; try setoid_rewrite IHC; auto. *)
(*   contradiction H. *)
(* Qed. *)

Lemma up_plug_ctx {Γ τi τm τo}
      (Co : (CTX Γ ⊢ [ Γ ⊢ τm ] : τo))
      (Ci : (CTX Γ ⊢ [ Γ ⊢ τi ] : τm))
      τ0 :
  (plug_ctx Co Ci)^^τ0 = plug_ctx (Co^^τ0) (Ci^^τ0).
Proof.
  intros.

  pose proof unchanged_env_means_simple Co as Co_simple.

  dependent induction Co;
    try specialize (IHCo Ci τ0 Co_simple);
    simpl in *;
    repeat destruct up_simple_ctx as [? [? ?]] in *;
    simpl in *;
    subst.
  {
    assert (x0 = c_hole) by (apply erase_ctx_injective; auto).
    subst.
    reflexivity.
  } {
    d_destruct x2; inject e3.
    d_destruct x3; inject e4.

    rewrite <- (expr_lift1_erase e τ0) in H1, H3.

    pose proof expr_type_unique _ _ H1.
    pose proof expr_type_unique _ _ H3.
    subst.
    elim_erase_eqs.
    simpl.
    f_equal.

    setoid_rewrite <- e5 in H0.
    setoid_rewrite <- e1 in H2.
    apply erase_ctx_injective.
    rewrite H0.

    rewrite (erase_ctx_injective H2).
    reflexivity.
  } {
    d_destruct x2; inject e3.
    d_destruct x3; inject e4.

    rewrite <- (expr_lift1_erase e τ0) in H0, H2.

    pose proof expr_type_unique _ _ H0.
    pose proof expr_type_unique _ _ H2.
    autoinjections.
    elim_erase_eqs.
    simpl.
    f_equal.

    setoid_rewrite <- e5 in H1.
    setoid_rewrite <- e1 in H3.
    apply erase_ctx_injective.
    rewrite H1.

    rewrite (erase_ctx_injective H3).
    reflexivity.
  } {
    d_destruct x2; inject e2.
    d_destruct x3; inject e3.

    simpl.
    f_equal.

    setoid_rewrite <- e in H0.
    setoid_rewrite <- e0 in H1.
    apply erase_ctx_injective.
    rewrite H0.

    rewrite (erase_ctx_injective H1).
    reflexivity.
  } {
    d_destruct x2; inject e3.
    d_destruct x3; inject e4.

    elim_erase_eqs.

    simpl.
    f_equal.

    setoid_rewrite <- e5 in H0.
    setoid_rewrite <- e1 in H2.
    apply erase_ctx_injective.
    rewrite H0.

    rewrite (erase_ctx_injective H2).
    reflexivity.
  } {
    d_destruct x2; inject e3.
    d_destruct x3; inject e4.

    elim_erase_eqs.

    simpl.
    f_equal.

    setoid_rewrite <- e5 in H1.
    setoid_rewrite <- e1 in H3.
    apply erase_ctx_injective.
    rewrite H1.

    rewrite (erase_ctx_injective H3).
    reflexivity.
  } {
    destruct Co_simple.
  }
Qed.

Lemma compat_plug {Γo τo Γh τh} e0 e1
      (C : CTX Γo ⊢ [Γh ⊢ τh] : τo) :
  (EXP Γh ⊢ e0 ≈ e1 : τh) ->
  (EXP Γo ⊢ C⟨e0⟩ ≈ C⟨e1⟩ : τo).
Proof.
  intros He.
  dependent induction C. {
    exact He.
  } {
    eapply compat_app; auto.
    reflexivity.
  } {
    eapply compat_app; auto.
    reflexivity.
  } {
    apply compat_factor; auto.
  } {
    apply compat_plus; auto.
    reflexivity.
  } {
    apply compat_plus; auto.
    reflexivity.
  } {
    apply compat_lam; auto.
  }
Qed.

Lemma erase_plug {Γo Γi τi τo} (C : (CTX Γo ⊢ [Γi ⊢ τi] : τo)) e :
  erase C⟨e⟩ = u_plug (erase_ctx C) (erase e).
Proof.
  induction C; simpl; try rewrite <- IHC; auto.
Qed.

Fixpoint is_u_simple (u : u_ctx) : Prop :=
  match u with
  | uc_hole => True

  | uc_app_l u' _
  | uc_app_r _ u'
  | uc_factor u'
  | uc_plus_l u' _
  | uc_plus_r _ u' => is_u_simple u'

  | uc_lam _ _ => False
  end.

Lemma rename_simple_u_plug (U : u_ctx) (u : u_expr) σ :
  is_u_simple U ->
  rename σ (u_plug U u) = u_plug (rename σ U) (rename σ u).
Proof.
  intro U_simp.
  induction U; simpl in *; try rewrite IHU; auto.
  contradiction U_simp.
Qed.

(* theorem 24 *)
Theorem subst_into_simple {Γ τe τo}
  (S : CTX Γ ⊢ [Γ ⊢ τe] : τo) :
  is_simple S ->
  forall (e : expr Γ τe),
    (EXP Γ ⊢ (λ, (S^τe)⟨var_0⟩) @ e ≈ S⟨e⟩ : τo).
Proof.
  intros S_simple e.

  refine (tc_ctx_single_rect
            (fun τh τ S' S_simple =>
               (* forall (τeq0 : τh = τe) *)
               (*        (τeq : τ = τo), *)
               forall (e : expr Γ τh),
                 (EXP Γ ⊢ (λ, (S' ^^ τh)⟨var_0⟩) @ e ≈ S'⟨e⟩ : τ)
            )
            _ _ _ _ _ S_simple _);
    clear;
    intros.
  {
    simpl.
    destruct up_simple_ctx as [? [? ?]]; simpl.
    assert (x = c_hole). {
      apply erase_ctx_injective.
      exact e0.
    }
    subst.
    apply apply_id_equiv.
  } {
    specialize (H e).

    transitivity ((λ, (S1^^τh)⟨(λ, ((S^^τh)^^τh)⟨var_0⟩) @ var_0⟩) @ e). {
      (* "by theorem 22" *)
      eapply compat_app; [| reflexivity].
      apply compat_lam.

      pose proof beta_value (((S^τh)^τh)⟨var_0⟩) var_0 I.
      pose proof single_is_simple _ S1_single as S1_simple.

      rewrite up_plug_ctx.
      rewrite plug_plug_ctx.

      symmetry.
      eapply compat_plug; eauto.

      repeat destruct open_subst1; simpl in *.
      repeat destruct up_simple_ctx as [? [? ?]]; simpl in *.

      assert (x0⟨var_0⟩ = x). {
        apply erase_injective.
        rewrite e0.
        rewrite !erase_plug.
        rewrite e2.

        simpl.

        clear_except i.
        replace (u_var 0 .: ids) with (ren pred); swap 1 2. {
          extensionality n.
          destruct n; auto.
        }
        rewrite <- rename_subst.

        rewrite rename_simple_u_plug. {
          f_equal.

          assert (forall e : u_expr, rename pred e↑ = e). {
            intros.
            asimpl.
            replace (ren ((+1) >>> pred)) with ids by auto.
            autosubst.
          }


          induction x0; simpl; f_equal; auto.
          contradiction i.
        } {
          induction x0; try contradiction i; simpl; auto.
        }
      }

      rewrite H1.
      exact H0.
    }

    transitivity (S1⟨(λ, (S^^τh)⟨var_0⟩) @ e⟩). {
      set (f := λ, (S^^_)⟨var_0⟩).
      replace (λ, ((S^^τh)^^τh)⟨var_0⟩) with (f^τh); swap 1 2. {
        revert S_simple; clear; intros.
        subst f.
        simpl.
        elim_sig_exprs.
        repeat destruct up_simple_ctx as [? [? ?]]; simpl in *.

        elim_erase_eqs.
        f_equal.

        apply erase_injective.
        rewrite erase_plug.
        rewrite e1, H0.
        rewrite erase_plug.
        rewrite e0.
        rewrite <- rename_subst.


        assert (is_u_simple (erase_ctx S) ↑). {
          rewrite <- e0.
          clear_except i.
          induction x; try contradiction i; auto.
        }
        rewrite rename_simple_u_plug; auto.
        simpl in *.
        f_equal.

        set (erase_ctx S) in *.
        clearbody u.
        revert H.
        clear.
        assert (forall e : u_expr, rename (0 .: (+2)) (e↑) = e↑↑)
          by (intros; autosubst).
        induction u; intros; simpl in *; f_equal; auto.
        contradiction H0.
      }

      assert (is_val f) by exact I.
      clearbody f.

      d_destruct S1; try d_destruct S1; try contradiction S1_single; auto.
      - apply single_frame_case_app_l; auto.
      - apply single_frame_case_app_r; auto.
      - apply single_frame_case_factor; auto.
      - apply single_frame_case_plus_l; auto.
      - apply single_frame_case_plus_r; auto.
    }

    rewrite plug_plug_ctx.
    erewrite compat_plug; eauto.
    reflexivity.
  }
Qed.

Print Assumptions subst_into_simple.
