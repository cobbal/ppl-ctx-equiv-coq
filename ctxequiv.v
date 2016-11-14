Require Import utils.
Require Import syntax.
Require Import relations.
Require Import properties_of_relations.
Require Import micromega.Lia.
Require Import List.


Inductive u_ctx :=
| uc_hole : u_ctx
| uc_app_l : u_ctx -> u_expr -> u_ctx
| uc_app_r : u_expr -> u_ctx -> u_ctx
| uc_factor : u_ctx -> u_ctx
| uc_plus_l : u_ctx -> u_expr -> u_ctx
| uc_plus_r : u_expr -> u_ctx -> u_ctx
| uc_lam : Ty -> {bind u_ctx} -> u_ctx
.

Reserved Notation "'CTX' Γo ⊢ [ Γh ⊢ τh ] : τo"
         (at level 70, no associativity).
Inductive ctx {Γh : Env Ty} {τh : Ty} : Env Ty -> Ty -> Type :=
| c_hole :
    (CTX Γh ⊢ [Γh ⊢ τh] : τh)
| c_app_l {Γ τa τr} :
    (CTX Γ ⊢ [Γh ⊢ τh] : (τa ~> τr)) ->
    expr Γ τa ->
    (CTX Γ ⊢ [Γh ⊢ τh] : τr)
| c_app_r {Γ τa τr} :
    expr Γ (τa ~> τr) ->
    (CTX Γ ⊢ [Γh ⊢ τh] : τa) ->
    (CTX Γ ⊢ [Γh ⊢ τh] : τr)
| c_factor {Γ} :
    (CTX Γ ⊢ [Γh ⊢ τh] : ℝ) ->
    (CTX Γ ⊢ [Γh ⊢ τh] : ℝ)
| c_plus_l {Γ} :
    (CTX Γ ⊢ [Γh ⊢ τh] : ℝ) ->
    expr Γ ℝ ->
    (CTX Γ ⊢ [Γh ⊢ τh] : ℝ)
| c_plus_r {Γ} :
    expr Γ ℝ ->
    (CTX Γ ⊢ [Γh ⊢ τh] : ℝ) ->
    (CTX Γ ⊢ [Γh ⊢ τh] : ℝ)
| c_lam {Γ τa τr} :
    (CTX (τa :: Γ) ⊢ [Γh ⊢ τh] : τr) ->
    (CTX Γ ⊢ [Γh ⊢ τh] : (τa ~> τr))
where "'CTX' Γo ⊢ [ Γh ⊢ τh ] : τo" := (@ctx Γh τh Γo τo).

Instance Rename_u_ctx : Rename u_ctx :=
  fix Rename_u_ctx σ C :=
    match C with
    | uc_hole => uc_hole
    | uc_app_l c0 e1 => uc_app_l (Rename_u_ctx σ c0) (rename σ e1)
    | uc_app_r e0 c1 => uc_app_r (rename σ e0) (Rename_u_ctx σ c1)
    | uc_factor c0 => uc_factor (Rename_u_ctx σ c0)
    | uc_plus_l c0 e1 => uc_plus_l (Rename_u_ctx σ c0) (rename σ e1)
    | uc_plus_r e0 c1 => uc_plus_r (rename σ e0) (Rename_u_ctx σ c1)
    | uc_lam τa cbody => uc_lam τa (Rename_u_ctx (upren σ) cbody)
    end.

Fixpoint u_plug (U : u_ctx) (e : u_expr) : u_expr :=
  match U with
  | uc_hole => e
  | uc_app_l c0 e1 => u_app (u_plug c0 e) e1
  | uc_app_r e0 c1 => u_app e0 (u_plug c1 e)
  | uc_factor c0 => u_factor (u_plug c0 e)
  | uc_plus_l c0 e1 => u_plus (u_plug c0 e) e1
  | uc_plus_r e0 c1 => u_plus e0 (u_plug c1 e)
  | uc_lam τa cbody => u_lam τa (u_plug cbody e)
  end.

Fixpoint plug {Γo Γh τh τo}
         (C : (CTX Γo ⊢ [ Γh ⊢ τh] : τo))
         (e : expr Γh τh)
  : expr Γo τo :=
  match C with
  | c_hole => e
  | c_app_l c0 e1 => e_app (plug c0 e) e1
  | c_app_r e0 c1 => e_app e0 (plug c1 e)
  | c_factor c0 => e_factor (plug c0 e)
  | c_plus_l c0 e1 => e_plus (plug c0 e) e1
  | c_plus_r e0 c1 => e_plus e0 (plug c1 e)
  | c_lam cbody => e_lam (plug cbody e)
  end.

Notation "C ⟨ e ⟩" := (plug C e)
  (at level 2, e at level 200, left associativity,
   format "C ⟨ e ⟩" ).

Fixpoint plug_ctx {Γo Γm Γi τi τm τo}
         (Co : (CTX Γo ⊢ [ Γm ⊢ τm ] : τo))
         (Ci : (CTX Γm ⊢ [ Γi ⊢ τi ] : τm))
  : (CTX Γo ⊢ [ Γi ⊢ τi ] : τo) :=
  match Co with
  | c_hole => Ci
  | c_app_l c0 e1 => c_app_l (plug_ctx c0 Ci) e1
  | c_app_r e0 c1 => c_app_r e0 (plug_ctx c1 Ci)
  | c_factor c0 => c_factor (plug_ctx c0 Ci)
  | c_plus_l c0 e1 => c_plus_l (plug_ctx c0 Ci) e1
  | c_plus_r e0 c1 => c_plus_r e0 (plug_ctx c1 Ci)
  | c_lam cbody => c_lam (plug_ctx cbody Ci)
  end.

Fixpoint erase_ctx {Γo Γi τi τo} (C : (CTX Γo ⊢ [Γi ⊢ τi] : τo)) : u_ctx :=
  match C with
  | c_hole => uc_hole
  | c_app_l c0 e1 => uc_app_l (erase_ctx c0) (erase e1)
  | c_app_r e0 c1 => uc_app_r (erase e0) (erase_ctx c1)
  | c_factor c => uc_factor (erase_ctx c)
  | c_plus_l c0 e1 => uc_plus_l (erase_ctx c0) (erase e1)
  | c_plus_r e0 c1 => uc_plus_r (erase e0) (erase_ctx c1)
  | @c_lam _ _ _ τa _ c => uc_lam τa (erase_ctx c)
  end.

Require Import FinFun.
Lemma erase_ctx_injective Γo Γi τi τo : Injective (@erase_ctx Γo Γi τi τo).
Proof.
  repeat intro.
  induction x;
    d_destruct (y, H);
    auto;
    try (erewrite IHx; eauto);
    try (erewrite erase_injective; eauto).
  {
    pose proof expr_type_unique _ _ x1.
    subst.
    erewrite IHx; eauto.
    erewrite erase_injective; eauto.
  } {
    pose proof expr_type_unique _ _ x.
    inversion H; subst.
    erewrite IHx; eauto.
    erewrite erase_injective; eauto.
  }
Qed.
Arguments erase_ctx_injective {_ _ _ _ _ _} _.

Lemma ctx_type_unique {Γo τo}
      {Γi0 τi0} (C0 : CTX Γo ⊢ [Γi0 ⊢ τi0] : τo)
      {Γi1 τi1} (C1 : CTX Γo ⊢ [Γi1 ⊢ τi1] : τo) :
  erase_ctx C0 = erase_ctx C1 ->
  Γi0 = Γi1 /\ τi0 = τi1.
Proof.
  intros Heq.
  revert_until C0.
  dependent induction C0; intros;
    dependent destruction C1;
    inversion Heq; subst;
      auto;
      try solve [eapply IHC0; eauto].
  {
    pose proof expr_type_unique _ _ H1.
    subst.
    eapply IHC0; eauto.
  } {
    pose proof expr_type_unique _ _ H0.
    inject H.
    eapply IHC0; eauto.
  }
Qed.

Definition ctx_equiv {Γ τ} (e0 e1 : expr Γ τ) :=
  forall (C : (CTX · ⊢ [Γ ⊢ τ] : ℝ)) A,
    μ C⟨e0⟩ A = μ C⟨e1⟩ A.

Lemma relation_sound {Γ τ} (e0 e1 : expr Γ τ) :
  (EXP Γ ⊢ e0 ≈ e1 : τ) ->
  ctx_equiv e0 e1.
Proof.
  intros re.

  repeat intro.

  set (A0 := A) at 1.
  set (A1 := A).

  assert (HA : A_rel ℝ A0 A1). {
    intros ? ? ?.
    rewrite Hv.
    auto.
  }
  clearbody A0 A1.
  clear A.

  revert C.
  enough (forall Γo ρC0 ρC1 (Hρ : G_rel Γo ρC0 ρC1)
                 (C : (CTX Γo ⊢ [Γ ⊢ τ] : ℝ)),
             μ (proj1_sig (close ρC0 C⟨e0⟩)) A0 =
             μ (proj1_sig (close ρC1 C⟨e1⟩)) A1); intros.
  {
    specialize (H _ _ _ G_rel_nil C).

    elim_sig_exprs.
    apply erase_injective in He.
    apply erase_injective in He2.
    subst.
    auto.
  }

  move Hρ after A0.
  induction C; simpl. {
    apply re; auto.
  } {
    specialize (IHC _ _ Hρ).
    pose proof (fundamental_property e _ _ Hρ).

    elim_sig_exprs.
    d_destruct (e6, He6).
    d_destruct (e7, He7).
    elim_erase_eqs.

    apply work_of_app; auto.
  } {
    specialize (IHC _ _ Hρ).
    pose proof (fundamental_property e _ _ Hρ).

    elim_sig_exprs.
    d_destruct (e6, He6).
    d_destruct (e7, He7).
    elim_erase_eqs.

    apply work_of_app; auto.
  } {
    specialize (IHC _ _ Hρ).

    elim_sig_exprs.
    d_destruct (e3, He3).
    d_destruct (e4, He4).
    elim_erase_eqs.

    apply work_of_factor; auto.
  } {
    specialize (IHC _ _ Hρ).
    pose proof (fundamental_property e _ _ Hρ).

    elim_sig_exprs.
    d_destruct (e6, He6).
    d_destruct (e7, He7).
    elim_erase_eqs.

    apply work_of_plus; auto.
  } {
    specialize (IHC _ _ Hρ).
    pose proof (fundamental_property e _ _ Hρ).

    elim_sig_exprs.
    d_destruct (e6, He6).
    d_destruct (e7, He7).
    elim_erase_eqs.

    apply work_of_plus; auto.
  } {
    elim_sig_exprs.
    d_destruct (e, He).
    d_destruct (e2, He2).

    change (μ (v_lam e) A0 = μ (v_lam e2) A1).
    rewrite 2 val_is_dirac.
    unfold dirac, indicator.
    f_equal.
    apply HA.

    constructor.
    intros.

    specialize (IHC _ _ (G_rel_cons H Hρ)).

    elim_sig_exprs.
    rewrite x0 in He5.
    rewrite x in He6.
    asimpl in He5.
    asimpl in He6.
    elim_erase_eqs.

    repeat intro.
    apply IHC.
    auto.
  }
Qed.

Lemma plug_plug_ctx {Γo Γm Γi τi τm τo}
      (Co : (CTX Γo ⊢ [Γm ⊢ τm] : τo))
      (Ci : (CTX Γm ⊢ [Γi ⊢ τi] : τm))
      (e : expr Γi τi) :
  (plug_ctx Co Ci)⟨e⟩ = Co⟨Ci⟨e⟩⟩.
Proof.
  induction Co; simpl; auto; rewrite IHCo; auto.
Qed.