(** In this file, we define contexts, contextual equivalence, and show that the
    logical relation [related_exprs] is sound with respect to contextual
    equivalence. *)
Require Import utils.
Require Import syntax.
Require Import relations.
Require Import properties_of_relations.
Require Import micromega.Lia.
Require Import List.
Require Export chain.


(** * Contexts

    A context is a [chain] of context frames.

    The notations below for types of frames and contexts should be thought of as
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

(* As before with expr, we define a (mostly) erased version of contexts and an
   injective erasure function from the fully typed context. *)
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

Set Typeclasses Unique Instances.

(** We can't instantiate all of autosubst's machinery for contexts, since they
    can't be variables, but we can at least define renaming. We could define
    substitution too, but the need for it hasn't come up yet. *)
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

(** ** The [Plug] typeclass *)
(** [Plug] should be thought of as a typeclass for plugging something into a
    context-like object using the syntax "[C⟨e⟩]". The machinery needed to do
    this is slightly more convoluted than it would be in Haskell. *)

(** Things we want to be able to plug (both for typed and untyped):
    - expressions into context frames
    - expressions into contexts
    - contexts into context
 *)
(** It would be possible to define even more combinations with frames, but they
    aren't yet needed. *)
Module Plug.
  Class Plug obj hole res :=
    mk {
        plug : obj -> hole -> res
      }.
  Arguments mk {_ _ _} _.
  Arguments plug {_ _ _ _} !_ _.
End Plug.

Notation "C ⟨ e ⟩" := (Plug.plug C e)
  (at level 2, e at level 200, left associativity,
   format "C ⟨ e ⟩" ).

Instance u_plug_frame : Plug.Plug u_ctx_frame u_expr u_expr :=
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

Instance u_plug' : Plug.Plug u_ctx u_expr u_expr := { plug := u_plug }.

Instance plug_frame {Γo τo Γh τh}
  : Plug.Plug (FRAME Γo ⊢ [Γh ⊢ τh] : τo) (expr Γh τh) (expr Γo τo) :=
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
  : Plug.Plug (CTX Γo ⊢ [Γh ⊢ τh] : τo) (expr Γh τh) (expr Γo τo) :=
  { plug C e := bichain_fold_right (fun _ _ _ _ C e => C⟨e⟩) e C }.

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

    dep_destruct (x, x1);
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

  dep_destruct (x, x0);
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

Lemma compat_plug1 {Γo τo Γh τh}
      (f : FRAME Γo ⊢ [Γh ⊢ τh] : τo)
      e0 e1 :
  (EXP Γh ⊢ e0 ≈ e1 : τh) ->
  (EXP Γo ⊢ f⟨e0⟩ ≈ f⟨e1⟩ : τo).
Proof.
  intros.
  dep_destruct f; cbn. {
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

Definition plug_cons {Γo τo Γm τm Γi τi}
      (f : (FRAME Γo ⊢ [Γm ⊢ τm] : τo))
      C (e : expr Γi τi) :
  (f :::: C)⟨e⟩ = f⟨C⟨e⟩⟩ := eq_refl.

Lemma compat_plug {Γo τo Γh τh}
      (C : CTX Γo ⊢ [Γh ⊢ τh] : τo)
      e0 e1 :
  (EXP Γh ⊢ e0 ≈ e1 : τh) ->
  (EXP Γo ⊢ C⟨e0⟩ ≈ C⟨e1⟩ : τo).
Proof.
  intros He.
  dependent induction C using bichain_rect. {
    exact He.
  } {
    change (EXP xA ⊢ x⟨C⟨e0⟩⟩ ≈ x⟨C⟨e1⟩⟩ : yA).
    apply compat_plug1.
    auto.
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

  pose proof compat_plug C e0 e1 re.
  specialize (H _ _ G_rel_nil).
  elim_sig_exprs.
  elim_erase_eqs.

  apply H.
  repeat intro.
  inject Hv.
  trivial.
Qed.