Require Import utils.
Require Import syntax.
Require Import relations.
Require Import properties_of_relations.
Require Import micromega.Lia.
Require Import List.


Inductive Ctx :=
| c_hole : Ctx
| c_app_l : Ctx -> Expr -> Ctx
| c_app_r : Expr -> Ctx -> Ctx
| c_factor : Ctx -> Ctx
| c_plus_l : Ctx -> Expr -> Ctx
| c_plus_r : Expr -> Ctx -> Ctx
| c_lam : Ty -> {bind Ctx} -> Ctx
.

Definition ctx_ty := Env Ty ⨉ Ty.

Reserved Notation "'TCX' Γo ⊢ C [ Γh => τh ] : τo"
         (at level 70, C at level 99, no associativity).
Inductive tc_ctx (Γh : Env Ty) (τh : Ty) : Ctx -> Env Ty -> Ty -> Type :=
| TCXHole :
    (TCX Γh ⊢ c_hole[Γh => τh] : τh)
| TCXApp_l {Γ τa τr c ea} :
    (TCX Γ ⊢ c[Γh => τh] : (τa ~> τr)) ->
    (TC Γ ⊢ ea : τa) ->
    (TCX Γ ⊢ (c_app_l c ea)[Γh => τh] : τr)
| TCXApp_r {Γ τa τr ef c} :
    (TC Γ ⊢ ef : τa ~> τr) ->
    (TCX Γ ⊢ c[Γh => τh] : τa) ->
    (TCX Γ ⊢ (c_app_r ef c)[Γh => τh] : τr)
| TCXFactor {Γ c} :
    (TCX Γ ⊢ c[Γh => τh] : ℝ) ->
    (TCX Γ ⊢ (c_factor c)[Γh => τh] : ℝ)
| TCXPlus_l {Γ c er} :
    (TCX Γ ⊢ c[Γh => τh] : ℝ) ->
    (TC Γ ⊢ er : ℝ) ->
    (TCX Γ ⊢ (c_plus_l c er)[Γh => τh] : ℝ)
| TCXPlus_r {Γ el c} :
    (TC Γ ⊢ el : ℝ) ->
    (TCX Γ ⊢ c[Γh => τh] : ℝ) ->
    (TCX Γ ⊢ (c_plus_r el c)[Γh => τh] : ℝ)
| TCXLam {Γ τa τr c} :
    (TCX (extend Γ τa) ⊢ c[Γh => τh] : τr) ->
    (TCX Γ ⊢ (c_lam τa c)[Γh => τh] : (τa ~> τr))
where "'TCX' Γo ⊢ C [ Γh => τh ] : τo" := (tc_ctx Γh τh C Γo τo).

Instance Rename_Ctx : Rename Ctx :=
  fix Rename_Ctx σ C :=
    match C with
    | c_hole => c_hole
    | c_app_l c0 e1 => c_app_l (Rename_Ctx σ c0) (rename σ e1)
    | c_app_r e0 c1 => c_app_r (rename σ e0) (Rename_Ctx σ c1)
    | c_factor c0 => c_factor (Rename_Ctx σ c0)
    | c_plus_l c0 e1 => c_plus_l (Rename_Ctx σ c0) (rename σ e1)
    | c_plus_r e0 c1 => c_plus_r (rename σ e0) (Rename_Ctx σ c1)
    | c_lam τa cbody => c_lam τa (Rename_Ctx (upren σ) cbody)
    end.
(* Instance Subst_Ctx : Subst Ctx := *)


(* Lemma ctx_ty_ren {Γo Γh C τh τo} : *)
(*   (TCX Γo ⊢ C[Γh => τh] : τo) -> *)
(*   forall Γo' ξ, *)
(*     lookup Γo = ξ >>> lookup Γo' -> *)
(*     (TCX Γo' ⊢ (rename ξ C)[Γh => τh] : τo). *)
(* Proof. *)
(*   induction 1; try solve [econstructor; eauto]; intros. { *)
(*     simpl. *)
(*     intros. *)
(*     rewrite H in e. *)
(*     simpl in e. *)
(*     constructor. *)
(*     auto. *)
(*   } { *)
(*     intros. *)
(*     constructor. *)
(*     set (ξ' x := match x with | O => O | S x => S (ξ x) end). *)
(*     assert (ren ξ' = up (ren ξ)). { *)
(*       subst ξ'. *)
(*       extensionality x. *)
(*       destruct x; auto. *)
(*     } *)
(*     rewrite <- H0. *)
(*     apply IHX. *)
(*     subst ξ'. *)
(*     extensionality x. *)
(*     simpl. *)
(*     rewrite H. *)
(*     simpl. *)
(*     destruct x; auto. *)
(*   } *)
(* Qed. *)

Lemma ty_subst {Γ e τ} :
  (TC Γ ⊢ e : τ) -> forall σ Δ,
    (forall x τ',
        lookup Γ x = Some τ' ->
        (TC Δ ⊢ σ x : τ')) ->
  (TC Δ ⊢ e.[σ] : τ).
Proof.
  induction 1; try solve [econstructor; eauto]; intros. {
    apply X.
    auto.
  } {
    constructor.
    apply IHX.
    intros [|]. {
      intros.
      simpl in *.
      constructor.
      auto.
    } {
      intros.
      simpl in H.
      specialize (X0 _ _ H).

      pose proof (ty_ren X0).
      specialize (X1 (extend Δ τa) S eq_refl).
      autosubst.
    }
  }
Qed.

Fixpoint plug (C : Ctx) (e : Expr) : Expr :=
  match C with
  | c_hole => e
  | c_app_l c0 e1 => e_app (plug c0 e) e1
  | c_app_r e0 c1 => e_app e0 (plug c1 e)
  | c_factor c0 => e_factor (plug c0 e)
  | c_plus_l c0 e1 => e_plus (plug c0 e) e1
  | c_plus_r e0 c1 => e_plus e0 (plug c1 e)
  | c_lam τa cbody => e_lam τa (plug cbody e)
  end.

Notation "C ⟨ e ⟩" := (plug C e)
  (at level 2, e at level 200, left associativity,
   format "C ⟨ e ⟩" ).

(* Notation "C [[ e ]]" := (plug C e) *)
(*   (at level 2, e at level 200, left associativity, *)
(*    format "C [[ e ]]" ). *)

Fixpoint plug_ctx (Co Ci : Ctx) : Ctx :=
  match Co with
  | c_hole => Ci
  | c_app_l c0 e1 => c_app_l (plug_ctx c0 Ci) e1
  | c_app_r e0 c1 => c_app_r e0 (plug_ctx c1 Ci)
  | c_factor c0 => c_factor (plug_ctx c0 Ci)
  | c_plus_l c0 e1 => c_plus_l (plug_ctx c0 Ci) e1
  | c_plus_r e0 c1 => c_plus_r e0 (plug_ctx c1 Ci)
  | c_lam τa cbody => c_lam τa (plug_ctx cbody Ci)
  end.

Lemma tc_plug {ΓC Γe τe τC C e} :
  (TC Γe ⊢ e : τe) ->
  (TCX ΓC ⊢ C[Γe => τe] : τC) ->
  (TC ΓC ⊢ C⟨e⟩ : τC).
Proof.
  intros He HC.
  induction HC; simpl; try econstructor; eauto.
Defined.

Lemma tc_plug_ctx
      {Γo Γm Γi}
      {τo τm τi}
      {Co Ci}
      (Ho : (TCX Γo ⊢ Co[Γm => τm] : τo))
      (Hi : (TCX Γm ⊢ Ci[Γi => τi] : τm)) :
  (TCX Γo ⊢ (plug_ctx Co Ci)[Γi => τi] : τo).
Proof.
  dependent induction Ho; try econstructor; eauto.
Defined.

Definition ctx_equiv {Γ τ e0 e1}
           (He0 : (TC Γ ⊢ e0 : τ))
           (He1 : (TC Γ ⊢ e1 : τ)) :=
  forall C (HC : (TCX · ⊢ C[Γ => τ] : ℝ)) A,
    μ (tc_plug He0 HC) A = μ (tc_plug He1 HC) A.

Lemma all_envs_inhabited Γ : inhabited (WT_Env Γ).
Proof.
  constructor.
  induction Γ. {
    exact WT_nil.
  } {
    apply extend_WT_Env; auto.
    induction a. {
      exact (v_real 0).
    } {
      exists (mk_Val (e_lam a1 IHa2) I).
      constructor.
      apply weaken.
      apply IHa2.
    }
  }
Qed.


Lemma related_close {Γ ρ0 ρ1}
      (Hρ : G_rel Γ ρ0 ρ1)
      {e0 e1 τ}
      (He0 : (TC Γ ⊢ e0 : τ))
      (He1 : (TC Γ ⊢ e1 : τ))
      (He : (EXP Γ ⊢ e0 ≈ e1 : τ)) :
  forall A0 A1,
    A_rel τ A0 A1 ->
    μ (close ρ0 He0) A0 = μ (close ρ1 He1) A1.
Proof.
  destruct He.
  intros A0 A1 HA.
  specialize (He _ _ Hρ).
  destruct He as [? ? He].
  replace (close ρ0 He0) with He4 by apply tc_unique.
  replace (close ρ1 He1) with He5 by apply tc_unique.
  apply He.
  auto.
Qed.

Lemma related_close1 {Γ ρ0 ρ1 e τ}
      (Hρ : G_rel Γ ρ0 ρ1)
      (He : (TC Γ ⊢ e : τ)) :
  forall A0 A1,
    A_rel τ A0 A1 ->
    μ (close ρ0 He) A0 = μ (close ρ1 He) A1.
Proof.
  intros.
  pose proof related_close Hρ He He (fundamental_property He).
  destruct (fundamental_property He) as [x x0 _].
  replace x with He in * by apply tc_unique.
  replace x0 with He in * by apply tc_unique.
  apply H0.
  auto.
Qed.

Lemma μ_rewrite {e e'}
  : e = e' ->
    forall τ He He',
    @μ e τ He = @μ e' τ He'.
Proof.
  intros.
  subst.
  f_equal.
  apply tc_unique.
Qed.

Lemma μ_apply {e0 e1 τ A He0 He1}
  (μeq : @μ e0 τ He0 A = @μ e1 τ He1 A)
  {e0' e1'}
  (Heq0 : e0 = e0')
  (Heq1 : e1 = e1')
  He0' He1' :
  @μ e0' τ He0' A = @μ e1' τ He1' A.
Proof.
  intros.
  subst.
  pose proof (expr_type_unique He0 He0').
  subst.
  pose proof (tc_unique He0 He0').
  pose proof (tc_unique He1 He1').
  subst.
  auto.
Qed.

Lemma close_nil {e τ} (He : TC · ⊢ e : τ)
  : μ (close WT_nil He) = μ He.
Proof.
  apply μ_rewrite.
  autosubst.
Qed.

Lemma relation_sound {Γ τ e0 e1}
      (He0 : (TC Γ ⊢ e0 : τ))
      (He1 : (TC Γ ⊢ e1 : τ)) :
  forall (re : (EXP Γ ⊢ e0 ≈ e1 : τ)),
    ctx_equiv He0 He1.
Proof.
  intros.
  pose proof re as re'.
  destruct re.
  pose proof (tc_unique He2 He0).
  pose proof (tc_unique He3 He1).
  subst.
  intros ? ? ?.
  pose (A0 := narrow_event A).
  pose (A1 := narrow_event A).
  assert (A_rel ℝ A0 A1). {
    repeat intro.
    simpl in Hv.
    destruct v0 using Val_rect; try contradiction Hv.
    destruct v1 using Val_rect; try contradiction Hv.
    simpl in *.
    inversion Hv.
    auto.
  }
  replace A with (A0 : Event (WT_Val ℝ)) at 1 by apply narrow_cast_inverse.
  replace A with (A1 : Event (WT_Val ℝ)) at 1 by apply narrow_cast_inverse.
  clearbody A0 A1.
  clear A.

  (* revert HCe0 HCe1. *)
  revert HC.

  enough (forall Γo ρC0 ρC1 (Hρ : G_rel Γo ρC0 ρC1)
                 (HC : (TCX Γo ⊢ C[Γ => τ] : ℝ)),
             μ (close ρC0 (tc_plug He0 HC)) A0 =
             μ (close ρC1 (tc_plug He1 HC)) A1). {

    intros.

    specialize (H0 _ _ _ G_rel_nil HC).
    (* do 2 set (close _ _) in H0. *)
    (* clearbody t t0. *)

    rewrite <- (close_nil (tc_plug He0 HC)).
    rewrite <- (close_nil (tc_plug He1 HC)).
    auto.
  }

  intros.
  revert Γo ρC0 ρC1 Hρ HC A0 A1 H re'.
  generalize ℝ as τC.

  dependent induction HC; intros; simpl in *. {
    destruct re' as [_ _ re].
    specialize (re _ _ Hρ).
    destruct re as [? ? re].
    specialize (re _ _ H).
    replace (close ρC0 He0) with He2 by apply tc_unique.
    replace (close ρC1 He1) with He3 by apply tc_unique.
    exact re.
  } {
    apply work_of_app; auto.
    apply related_close1; auto.
  } {
    apply work_of_app; auto.
    apply related_close1; auto.
  } {
    apply work_of_factor; auto.
  } {
    apply work_of_plus; auto.
    apply related_close1; auto.
  } {
    apply work_of_plus; auto.
    apply related_close1; auto.
  } {
    do 2 set (TCLam _).
    enough (dirac (WT_Val_of_pure t I) A0 =
            dirac (WT_Val_of_pure t0 I) A1). {
      subst t t0.
      rewrite <- 2 (pure_is_dirac (TCLam _) I) in H0.
      exact H0.
    }

    unfold dirac, Indicator; simpl.
    f_equal.
    apply H.

    split; auto.
    inversion t.
    inversion t0.
    subst.
    exists X; eauto.
    exists X0; eauto.
    clear t t0.
    rename X into Hplug0.
    rename X0 into Hplug1.

    intros va0 va1 Hva.
    exists (ty_subst1 va0 Hplug0) (ty_subst1 va1 Hplug1).
    intros Ar0 Ar1 HAr.

    specialize (IHHC _ _ (extend_grel _ _ Hρ Hva)).
    specialize (IHHC _ _ HAr re').

    (* ick *)
    set c⟨e0⟩.[up (subst_of_WT_Env ρC0)].[va0 : Expr/].
    set c⟨e0⟩.[subst_of_WT_Env (extend_WT_Env ρC0 va0)].
    assert (y = y0) by (subst y y0; autosubst).
    rewrite (μ_rewrite
               H0 τr
               (ty_subst1 va0 Hplug0)
               (close (extend_WT_Env ρC0 va0) (tc_plug He0 HC))).
    repeat subst.
    clear H0.

    set c⟨e1⟩.[up (subst_of_WT_Env ρC1)].[va1 : Expr/].
    set c⟨e1⟩.[subst_of_WT_Env (extend_WT_Env ρC1 va1)].
    assert (y = y0) by (subst y y0; autosubst).
    rewrite (μ_rewrite
               H0 τr
               (ty_subst1 va1 Hplug1)
               (close (extend_WT_Env ρC1 va1) (tc_plug He1 HC))).
    repeat subst.
    clear H0.
    auto.
  }
Qed.


Fixpoint ctx_of_env {Γ ρ} (Hρ : TCEnv ρ Γ) : Ctx :=
  match Hρ with
  | TCENil => c_hole
  | @TCECons v τ _ _ _ Hρ' =>
    plug_ctx (ctx_of_env Hρ') (c_app_l (c_lam τ c_hole) v)
  end.

Lemma ctx_of_env_tc :
  forall {Γ ρ τ} (Hρ : TCEnv ρ Γ),
    (TCX · ⊢ (ctx_of_env Hρ)[Γ => τ] : τ).
Proof.
  enough (forall {Γo Γi ρ τ} (Hρ : TCEnv ρ Γi),
             (TCX Γo ⊢ (ctx_of_env Hρ)[Γi ++ Γo => τ] : τ)). {
    intros.
    specialize (X · Γ ρ τ Hρ).
    rewrite app_nil_r in X.
    exact X.
  }

  intros.

  induction Hρ; intros. {
    constructor.
  } {
    simpl.
    apply (tc_plug_ctx IHHρ).
    repeat econstructor.
    exact (weaken t).
  }
Qed.

Lemma plug_plug_ctx C0 C1 e : (plug_ctx C0 C1)⟨e⟩ = plug C0 (C1⟨e⟩).
Proof.
  induction C0; simpl; auto; try rewrite IHC0; auto.
Qed.

Lemma relation_complete {Γ τ e0 e1}
      (He0 : TC Γ ⊢ e0 : τ)
      (He1 : TC Γ ⊢ e1 : τ) :
  ctx_equiv He0 He1 ->
  (EXP Γ ⊢ e0 ≈ e1 : τ).
Proof.
  intros.
  refine (mk_related_exprs He0 He1 _).
  intros ρ0 ρ1 Hρ.
  apply same_substitution_suffices; auto.
  intros ρ.
  clear ρ0 ρ1 Hρ.

  induction τ. {
    specialize (H _ (ctx_of_env_tc (WT_Env_tc ρ))).
    exists (close ρ He0) (close ρ He1).
    intros.
    setoid_rewrite (A_rel_subidentity H0).
    clear A0 H0.

    set (A := (A1 : Event (WT_Val ℝ))) in *.
    clearbody A.
    clear A1.

    destruct ρ as [ρ Hρ].
    simpl in *.

    revert e0 e1 He0 He1 H.

    induction Hρ; intros. {
      rewrite 2 close_nil.
      do 2 set (tc_plug _ _) in H.
      clearbody t t0.
      simpl in *.
      rewrite (tc_unique He0 t).
      rewrite (tc_unique He1 t0).
      apply H.
    } {
      do 2 set (tc_plug _ _) in H.
      clearbody t0 t1.
      simpl in *.
      specialize (IHHρ _ _
                       (TCApp (TCLam He0) (weaken t))
                       (TCApp (TCLam He1) (weaken t))).

      assert (forall A : Event (WT_Val ℝ),
                 μ (tc_plug (TCApp (TCLam He0) (weaken t)) (ctx_of_env_tc Hρ)) A =
                 μ (tc_plug (TCApp (TCLam He1) (weaken t)) (ctx_of_env_tc Hρ)) A). {
        clear IHHρ.
        intros.

        assert (forall e,
                   (plug_ctx (ctx_of_env Hρ) (c_app_l (c_lam τ c_hole) v))⟨e⟩ =
                   (ctx_of_env Hρ)⟨e_app (e_lam τ e) v⟩). {
          intros.
          clear.
          apply plug_plug_ctx.
        }
        erewrite <- (μ_rewrite (H0 e0)).
        erewrite <- (μ_rewrite (H0 e1)).
        apply H.
      }

      specialize (IHHρ H0).
      apply (μ_apply IHHρ). {
Abort.