Require Import utils.
Require Import syntax.
Require Import relations.
Require Import properties_of_relations.
Require Import micromega.Lia.
Require Import List.
Require Export chain.

(* A context is a chain (see chain.v) of context frames. As before with expr, we
   define a (mostly) erased version and an injective erasure function from the
   fully typed context *)

Inductive u_ctx_frame :=
| uc_app_f (ua : u_expr)
| uc_app_a (uf : u_expr)
| uc_factor
| uc_plus_l (ur : u_expr)
| uc_plus_r (ul : u_expr)
| uc_lam (τa : Ty)
.

Definition u_ctx := list u_ctx_frame.
Definition uc_hole : u_ctx := nil.

(* The notation below for types of frames and contexts should be thought of as
   "contexts take terms sitting in a hole typed `Γh ⊢ τh` and translate them to
   sit at type `Γo ⊢ τo`". The outermost chain_cons is the outermost context
   frame here. *)

Reserved Notation "'FRAME' Γo ⊢ [ Γh ⊢ τh ] : τo"
         (at level 70, Γo, Γh, τh, τo at level 200, no associativity).
Reserved Notation "'CTX' Γo ⊢ [ Γh ⊢ τh ] : τo"
         (at level 70, Γo, Γh, τh, τo at level 200, no associativity).

Inductive ctx_frame : Env Ty -> Ty -> Env Ty -> Ty -> Type :=
| c_app_f {Γ τa τr} :
    expr Γ τa ->
    (FRAME Γ ⊢ [Γ ⊢ τa ~> τr] : τr)
| c_app_a {Γ τa τr} :
    expr Γ (τa ~> τr) ->
    (FRAME Γ ⊢ [Γ ⊢ τa] : τr)
| c_factor {Γ} :
    (FRAME Γ ⊢ [Γ ⊢ ℝ] : ℝ)
| c_plus_l {Γ} :
    expr Γ ℝ ->
    (FRAME Γ ⊢ [Γ ⊢ ℝ] : ℝ)
| c_plus_r {Γ} :
    expr Γ ℝ ->
    (FRAME Γ ⊢ [Γ ⊢ ℝ] : ℝ)
| c_lam {Γ τa τr} :
    (FRAME Γ ⊢ [τa :: Γ ⊢ τr] : τa ~> τr)
where "'FRAME' Γo ⊢ [ Γh ⊢ τh ] : τo" := (ctx_frame Γo τo Γh τh).

Definition ctx := bichain ctx_frame.
Notation "'CTX' Γo ⊢ [ Γh ⊢ τh ] : τo" := (ctx Γo τo Γh τh).
Definition c_hole {Γ τ} : (CTX Γ ⊢ [Γ ⊢ τ] : τ) := chain_nil.

Set Typeclasses Unique Instances.

Instance Rename_u_ctx_frame : Rename u_ctx_frame :=
  fun σ f =>
    match f with
    | uc_app_f ea => uc_app_f (rename σ ea)
    | uc_app_a ef => uc_app_a (rename σ ef)
    | uc_factor => uc_factor
    | uc_plus_l er => uc_plus_l (rename σ er)
    | uc_plus_r el => uc_plus_r (rename σ el)
    | uc_lam τa => uc_lam τa
    end.

Instance Rename_u_ctx : Rename u_ctx :=
  fix Rename_u_ctx σ U :=
    match U with
    | nil => nil
    | f :: U' => rename σ f :: Rename_u_ctx σ U'
    end.

Module Plug.
  Class type obj hole res :=
    mk {
        plug : obj -> hole -> res
      }.
  Arguments mk {_ _ _} _.
  Arguments plug {_ _ _ _} !_ _.
End Plug.

Notation "C ⟨ e ⟩" := (Plug.plug C e)
  (at level 2, e at level 200, left associativity,
   format "C ⟨ e ⟩" ).

Instance u_plug_frame : Plug.type u_ctx_frame u_expr u_expr :=
  { plug f e :=
      match f with
      | uc_app_f ea => u_app e ea
      | uc_app_a ef => u_app ef e
      | uc_factor => u_factor e
      | uc_plus_l er => u_plus e er
      | uc_plus_r el => u_plus el e
      | uc_lam τa => u_lam τa e
      end
  }.

Fixpoint u_plug (U : u_ctx) (e : u_expr) : u_expr :=
  match U with
  | nil => e
  | f :: U' => f⟨u_plug U' e⟩
  end.

Instance u_plug' : Plug.type u_ctx u_expr u_expr := { plug := u_plug }.

Instance plug_frame {Γo τo Γh τh}
  : Plug.type (FRAME Γo ⊢ [Γh ⊢ τh] : τo) (expr Γh τh) (expr Γo τo) :=
  { plug f :=
      match f in (FRAME Γo' ⊢ [Γh' ⊢ τh'] : τo')
            return (expr Γh' τh' -> expr Γo' τo') with
      | c_app_f ea => fun e => e_app e ea
      | c_app_a ef => fun e => e_app ef e
      | c_factor => fun e => e_factor e
      | c_plus_l er => fun e => e_plus e er
      | c_plus_r el => fun e => e_plus el e
      | c_lam => fun e => e_lam e
      end
  }.

Instance plug {Γo τo Γh τh}
  : Plug.type (CTX Γo ⊢ [Γh ⊢ τh] : τo) (expr Γh τh) (expr Γo τo) :=
  { plug C e := bichain_fold_right (fun _ _ _ _ C e => C⟨e⟩) e C }.

Lemma plug_cons {Γo τo Γm τm Γi τi}
      (f : (FRAME Γo ⊢ [Γm ⊢ τm] : τo))
      C (e : expr Γi τi) :
  (f :::: C)⟨e⟩ = f⟨C⟨e⟩⟩.
Proof.
  trivial.
Qed.

Definition erase_ctx_frame {Γo τo Γh τh} (f : (FRAME Γo ⊢ [Γh ⊢ τh] : τo))
  : u_ctx_frame :=
  match f with
  | c_app_f ea => uc_app_f (erase ea)
  | c_app_a ef => uc_app_a (erase ef)
  | c_factor => uc_factor
  | c_plus_l er => uc_plus_l (erase er)
  | c_plus_r el => uc_plus_r (erase el)
  | @c_lam _ τa _ => uc_lam τa
  end.

Definition erase_ctx {Γo τo Γh τh} (C : (CTX Γo ⊢ [Γh ⊢ τh] : τo)) : u_ctx :=
  bichain_to_list (@erase_ctx_frame) C.

Lemma erase_cons {Γo τo Γm τm Γi τi}
      (f : (FRAME Γo ⊢ [Γm ⊢ τm] : τo))
      (C : (CTX Γm ⊢ [Γi ⊢ τi] : τm)) :
  erase_ctx (f :::: C) = erase_ctx_frame f :: erase_ctx C.
Proof.
  trivial.
Qed.

Require Import FinFun.
Lemma erase_ctx_injective {Γo τo Γh τh} : Injective (@erase_ctx Γo τo Γh τh).
Proof.
  repeat intro.

  revert y H.
  induction x using bichain_rect; intros. {
    cbn in *.
    dependent destruction y0 using bichain_rect; try discriminate.
    reflexivity.
  } {
    dependent destruction y using bichain_rect; try discriminate.
    rewrite !erase_cons in H.
    inject H.

    d_destruct (x, x1);
      try discriminate H1;
      f_equal;
      auto;
      inject H1;
      try (erewrite erase_injective; eauto).
    {
      pose proof expr_type_unique _ _ H0.
      subst.
      erewrite IHx; eauto.
      f_equal.
      erewrite erase_injective; eauto.
    } {
      pose proof expr_type_unique _ _ H0.
      inject H.
      erewrite IHx; eauto.
      f_equal.
      erewrite erase_injective; eauto.
    }
  }
Qed.
Arguments erase_ctx_injective {_ _ _ _ _ _} _.

Lemma ctx_type_unique {Γo τo}
      {Γi τi} (C : (CTX Γo ⊢ [Γi ⊢ τi] : τo))
      {Γi' τi'} (C' : (CTX Γo ⊢ [Γi' ⊢ τi'] : τo)) :
  erase_ctx C = erase_ctx C' ->
  Γi = Γi' /\ τi = τi'.
Proof.
  intros Heq.
  revert_until C.
  dependent induction C using bichain_rect;
    intros;
    dependent destruction C' using bichain_rect;
    inversion Heq;
    subst;
    auto.
  change (erase_ctx C = erase_ctx C') in H1.

  d_destruct (x, x0);
    try inject Heq;
    try solve [eapply IHC; eauto].
  {
    pose proof expr_type_unique _ _ H2.
    subst.
    eapply IHC; eauto.
  } {
    pose proof expr_type_unique _ _ H2.
    inject H.
    eapply IHC; eauto.
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
  induction C using bichain_rect. {
    apply re; auto.
  } {
    specialize (IHC _ _ re).
    rewrite !plug_cons.
    destruct x; try specialize (IHC _ _ Hρ). {
      pose proof (fundamental_property e _ _ Hρ).

      elim_sig_exprs.
      d_destruct (e6, He6).
      d_destruct (e7, He7).
      elim_erase_eqs.

      apply work_of_app; auto.
    } {
      pose proof (fundamental_property e _ _ Hρ).

      elim_sig_exprs.
      d_destruct (e6, He6).
      d_destruct (e7, He7).
      elim_erase_eqs.

      apply work_of_app; auto.
    } {
      elim_sig_exprs.
      d_destruct (e3, He3).
      d_destruct (e4, He4).
      elim_erase_eqs.

      apply work_of_factor; auto.
    } {
      pose proof (fundamental_property e _ _ Hρ).

      elim_sig_exprs.
      d_destruct (e6, He6).
      d_destruct (e7, He7).
      elim_erase_eqs.

      apply work_of_plus; auto.
    } {
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

      rewrite !rewrite_v_lam.
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
  }
Qed.