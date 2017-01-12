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
| uc_app_f (ϕ : Effect) (ua : u_expr)
| uc_app_a (uf : u_expr)
| uc_factor
| uc_observe_l (ur : u_expr)
| uc_observe_r (ul : u_expr)
| uc_binop_l (op : binop) (ur : u_expr)
| uc_binop_r (op : binop) (ul : u_expr)
| uc_lam (τa : Ty)
| uc_hide
.

Definition u_ctx := list u_ctx_frame.
Definition uc_hole : u_ctx := nil.

(* The notation below for types of frames and contexts should be thought of as
   "contexts take terms sitting in a hole typed `Γh ⊢ τh` and translate them to
   sit at type `Γo ⊢ τo`". The outermost chain_cons is the outermost context
   frame here. *)

Reserved Notation "'FRAME' Γo ⊢ [ Γh ⊢ τh , ϕh ] : τo , ϕo"
         (at level 70, Γo, Γh, τh, τo, ϕh, ϕo at level 200, no associativity).
Reserved Notation "'CTX' Γo ⊢ [ Γh ⊢ τh , ϕh ] : τo , ϕo"
         (at level 70, Γo, Γh, τh, τo at level 200, no associativity).

Inductive ctx_frame : Env Ty -> Ty -> Effect -> Env Ty -> Ty -> Effect -> Type :=
| c_app_f {Γ τa ϕ τr ϕf ϕa} :
    expr Γ τa ϕa ->
    (FRAME Γ ⊢ [Γ ⊢ τa ~~ ϕ ~> τr, ϕf] : τr, ϕ)
| c_app_a {Γ τa ϕ τr ϕf ϕa} :
    expr Γ (τa ~~ ϕ ~> τr) ϕf ->
    (FRAME Γ ⊢ [Γ ⊢ τa, ϕa] : τr, ϕ)
| c_factor {Γ ϕ} :
    (FRAME Γ ⊢ [Γ ⊢ ℝ, ϕ] : ℝ, ObsNone)
| c_observe_l {Γ ϕl} :
    expr Γ ℝ ObsR ->
    (FRAME Γ ⊢ [Γ ⊢ ℝ, ϕl] : ℝ, ObsNone)
| c_observe_r {Γ ϕl} :
    expr Γ ℝ ϕl ->
    (FRAME Γ ⊢ [Γ ⊢ ℝ, ObsR] : ℝ, ObsNone)
| c_binop_l {Γ ϕl ϕr} :
    binop ->
    expr Γ ℝ ϕr ->
    (FRAME Γ ⊢ [Γ ⊢ ℝ, ϕl] : ℝ, ϕr)
| c_binop_r {Γ ϕl ϕr} :
    binop ->
    expr Γ ℝ ϕl ->
    (FRAME Γ ⊢ [Γ ⊢ ℝ, ϕr] : ℝ, ϕr)
| c_lam {Γ τa ϕ τr} :
    (FRAME Γ ⊢ [τa :: Γ ⊢ τr, ϕ] : τa ~~ ϕ ~> τr, ObsNone)
| c_hide {Γ} :
    (FRAME Γ ⊢ [Γ ⊢ ℝ, ObsR] : ℝ, ObsNone)
where "'FRAME' Γo ⊢ [ Γh ⊢ τh , ϕh ] : τo , ϕo" := (ctx_frame Γo τo ϕo Γh τh ϕh).

Definition ctx := trichain ctx_frame.
Notation "'CTX' Γo ⊢ [ Γh ⊢ τh , ϕh ] : τo , ϕo" := (ctx Γo τo ϕo Γh τh ϕh).
Definition c_hole {Γ τ ϕ} : (CTX Γ ⊢ [Γ ⊢ τ, ϕ] : τ , ϕ) := chain_nil.

Set Typeclasses Unique Instances.

Instance Rename_u_ctx_frame : Rename u_ctx_frame :=
  fun σ f =>
    match f with
    | uc_app_f ϕ ea => uc_app_f ϕ (rename σ ea)
    | uc_app_a ef => uc_app_a (rename σ ef)
    | uc_factor => uc_factor
    | uc_observe_l er => uc_observe_l (rename σ er)
    | uc_observe_r el => uc_observe_r (rename σ el)
    | uc_binop_l op er => uc_binop_l op (rename σ er)
    | uc_binop_r op el => uc_binop_r op (rename σ el)
    | uc_lam τa => uc_lam τa
    | uc_hide => uc_hide
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
      | uc_app_f _ ea => u_app e ea
      | uc_app_a ef => u_app ef e
      | uc_factor => u_factor e
      | uc_observe_l er => u_observe e er
      | uc_observe_r el => u_observe el e
      | uc_binop_l op er => u_binop op e er
      | uc_binop_r op el => u_binop op el e
      | uc_lam τa => u_lam τa e
      | uc_hide => u_hide_observable e
      end
  }.

Fixpoint u_plug (U : u_ctx) (e : u_expr) : u_expr :=
  match U with
  | nil => e
  | f :: U' => f⟨u_plug U' e⟩
  end.

Instance u_plug' : Plug.type u_ctx u_expr u_expr := { plug := u_plug }.

Instance plug_frame {Γo τo ϕo Γh τh ϕh}
  : Plug.type (FRAME Γo ⊢ [Γh ⊢ τh, ϕh] : τo, ϕo) (expr Γh τh ϕh) (expr Γo τo ϕo) :=
  { plug f :=
      match f in (FRAME Γo' ⊢ [Γh' ⊢ τh', ϕh'] : τo', ϕo')
            return (expr Γh' τh' ϕh' -> expr Γo' τo' ϕo') with
      | c_app_f ea => fun e => e_app e ea
      | c_app_a ef => fun e => e_app ef e
      | c_factor => fun e => e_factor e
      | c_observe_l er => fun e => e_observe e er
      | c_observe_r el => fun e => e_observe el e
      | c_binop_l op er => fun e => e_binop op e er
      | c_binop_r op el => fun e => e_binop op el e
      | c_lam => fun e => e_lam e
      | c_hide => fun e => e_hide_observable e
      end
  }.

Instance plug {Γo τo ϕo Γh τh ϕh}
  : Plug.type (CTX Γo ⊢ [Γh ⊢ τh, ϕh] : τo, ϕo) (expr Γh τh ϕh) (expr Γo τo ϕo) :=
  { plug C e := trichain_fold_right (fun _ _ _ _ _ _ C e => C⟨e⟩) e C }.

Lemma plug_cons {Γo τo ϕo Γm τm ϕm Γi τi ϕi}
      (f : (FRAME Γo ⊢ [Γm ⊢ τm, ϕm] : τo, ϕo))
      C (e : expr Γi τi ϕi) :
  (f :3: C)⟨e⟩ = f⟨C⟨e⟩⟩.
Proof.
  trivial.
Qed.

Definition erase_ctx_frame {Γo τo ϕo Γh τh ϕh} (f : (FRAME Γo ⊢ [Γh ⊢ τh, ϕh] : τo, ϕo))
  : u_ctx_frame :=
  match f with
  | @c_app_f _ _ ϕ _ _ _ ea => uc_app_f ϕ (erase ea)
  | c_app_a ef => uc_app_a (erase ef)
  | c_factor => uc_factor
  | c_observe_l er => uc_observe_l (erase er)
  | c_observe_r el => uc_observe_r (erase el)
  | c_binop_l op er => uc_binop_l op (erase er)
  | c_binop_r op el => uc_binop_r op (erase el)
  | @c_lam _ τa _ => uc_lam τa
  | c_hide => uc_hide
  end.

Definition erase_ctx {Γo τo ϕo Γh τh ϕh} (C : (CTX Γo ⊢ [Γh ⊢ τh, ϕh] : τo, ϕo)) : u_ctx :=
  trichain_to_list (@erase_ctx_frame) C.

Lemma erase_cons {Γo τo ϕo Γm τm ϕm Γi τi ϕi}
      (f : (FRAME Γo ⊢ [Γm ⊢ τm, ϕm] : τo, ϕo))
      (C : (CTX Γm ⊢ [Γi ⊢ τi, ϕi] : τm, ϕm)) :
  erase_ctx (f :3: C) = erase_ctx_frame f :: erase_ctx C.
Proof.
  trivial.
Qed.

Definition ctx_equiv {Γ τ ϕ} (e0 e1 : expr Γ τ ϕ) :=
  forall (C : (CTX · ⊢ [Γ ⊢ τ, ϕ] : ℝ, ObsNone)) A,
    μ C⟨e0⟩ A = μ C⟨e1⟩ A.

(* This definition is equivalent to the previous one, but can be easier to work with *)
Definition ctx_equiv_by_both_μs {Γ τ ϕ} (e0 e1 : expr Γ τ ϕ) :=
  forall ϕo (C : (CTX · ⊢ [Γ ⊢ τ, ϕ] : ℝ, ϕo)),
    (forall A, μ C⟨e0⟩ A = μ C⟨e1⟩ A) /\
    (forall v A (H : ϕo = ObsR),
        let C' := (rew [fun ϕo => CTX · ⊢ [Γ ⊢ τ, ϕ] : ℝ, ϕo] H in C) in
        obs_μ C'⟨e0⟩ v A = obs_μ C'⟨e1⟩ v A).

Lemma ctx_equivs_equiv {Γ τ ϕ} (e0 e1 : expr Γ τ ϕ) :
  ctx_equiv e0 e1 <-> ctx_equiv_by_both_μs e0 e1.
Proof.
  split; repeat intro. {
    destruct ϕo; [| split; intros; auto; discriminate].

    pose proof (H (c_hide :3: C)).
    change (forall A, μ (e_hide_observable C⟨e0⟩) A = μ (e_hide_observable C⟨e1⟩) A) in H0.
    rewrite 2 μ_hide in H0.
    split; auto.

    intros; subst.
    d_destruct H1.
    cbn in C'.
    subst C'.

    rewrite 2 μ_of_obs_μ.
    f_equal.
    apply (H (c_observe_r v :3: C)).
  } {
    destruct (H _ C); auto.
  }
Qed.

Lemma compat_plug1 {Γo τo ϕo Γh τh ϕh}
      (f : FRAME Γo ⊢ [Γh ⊢ τh, ϕh] : τo, ϕo)
      e0 e1 :
  (EXP Γh ⊢ e0 ≈ e1 : τh, ϕh) ->
  (EXP Γo ⊢ f⟨e0⟩ ≈ f⟨e1⟩ : τo, ϕo).
Proof.
  intros.
  d_destruct f; cbn;
    apply compat_app ||
    apply compat_factor ||
    apply compat_observe ||
    apply compat_binop ||
    apply compat_plus ||
    apply compat_lam ||
    apply compat_hide;
    auto;
    reflexivity.
Qed.

Lemma compat_plug {Γo τo ϕo Γh τh ϕh}
      (C : CTX Γo ⊢ [Γh ⊢ τh, ϕh] : τo, ϕo)
      e0 e1 :
  (EXP Γh ⊢ e0 ≈ e1 : τh, ϕh) ->
  (EXP Γo ⊢ C⟨e0⟩ ≈ C⟨e1⟩ : τo, ϕo).
Proof.
  intros He.
  dependent induction C using trichain_rect. {
    exact He.
  } {
    rewrite !plug_cons.
    apply compat_plug1.
    auto.
  }
Qed.

Lemma relation_sound {Γ τ ϕ} (e0 e1 : expr Γ τ ϕ) :
  (EXP Γ ⊢ e0 ≈ e1 : τ, ϕ) ->
  ctx_equiv e0 e1.
Proof.
  intros re.

  repeat intro.

  pose proof compat_plug C e0 e1 re.
  specialize (H _ _ G_rel_nil).
  rewrite !close_nil in H.
  apply H.

  repeat intro.
  hnf in Hv.
  subst.
  auto.
Qed.