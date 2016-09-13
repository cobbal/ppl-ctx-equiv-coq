Require Import Reals.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics.
Require Import nnr.
Require Import utils.

Local Open Scope R.

Parameter Var : Type.
Parameter Var_eq_dec : forall x y : Var, {x = y} + {x <> y}.

Inductive Ty :=
| ℝ : Ty
| Arrow : Ty -> Ty -> Ty
.
Notation "x ~> y" := (Arrow x y) (at level 69, right associativity, y at level 70).

Inductive Expr :=
| e_app : Expr -> Expr -> Expr
| e_factor : Expr -> Expr
| e_sample : Expr
| e_plus : Expr -> Expr -> Expr
| e_pure : AExpr -> Expr
with AExpr :=
| e_real : R -> AExpr
| e_lam : Var -> Expr -> AExpr
| e_var : Var -> AExpr
.

Definition Env (T : Type) := Var -> option T.
Definition empty_env {T : Type} : Env T := const None.
Definition extend {T} (ρ : Env T) (x : Var) (v : T) : Env T :=
  fun y => if Var_eq_dec x y then Some v else ρ x.
(* Notation "ρ [ x → v ]" := (extend ρ x v) (at level 68, left associativity). *)

Reserved Notation "'TC' Γ ⊢ e : τ" (at level 70, e at level 99, no associativity).
Inductive tc {Γ : Env Ty} : Expr -> Ty -> Type :=
| TCReal (r : R)
  : (TC Γ ⊢ e_pure (e_real r) : ℝ)
| TCVar {x : Var} {τ : Ty}
  : Γ x = Some τ ->
    (TC Γ ⊢ e_pure (e_var x) : τ)
| TCLam {x : Var} {τa τr : Ty} {body : Expr}
  : (TC (extend Γ x τa) ⊢ body : τr) ->
    (TC Γ ⊢ e_pure (e_lam x body) : τa ~> τr)
| TCApp {e0 e1 : Expr} {τa τr : Ty}
  : (TC Γ ⊢ e0 : τa ~> τr) ->
    (TC Γ ⊢ e1 : τa) ->
    (TC Γ ⊢ e_app e0 e1 : τr)
| TCFactor {e : Expr}
  : (TC Γ ⊢ e : ℝ) ->
    (TC Γ ⊢ e_factor e : ℝ)
| TCSample
  : (TC Γ ⊢ e_sample : ℝ)
| TCPlus {e0 e1 : Expr}
  : (TC Γ ⊢ e0 : ℝ) ->
    (TC Γ ⊢ e1 : ℝ) ->
    (TC Γ ⊢ e_plus e0 e1 : ℝ)
where "'TC' Γ ⊢ e : τ" := (tc (Γ := Γ) e τ).

Inductive Val :=
| v_real : R -> Val
| v_clo : Var -> Expr -> Env Val -> Val
.

Definition env_dom_eq {A B} (envA : Env A) (envB : Env B) :=
  forall x, envA x = None <-> envB x = None.

Definition env_search {A B} {envA : Env A} {envB : Env B} :
  env_dom_eq envA envB ->
  forall x a,
    envA x = Some a ->
    {b | envB x = Some b}.
Proof.
  intros.
  specialize (H x).
  destruct H.
  destruct (envB x). {
    exists b; auto.
  } {
    specialize (H1 eq_refl).
    rewrite H1 in *.
    inversion H0.
  }
Defined.

(* Record env_models' {R : Val -> Ty -> Type} {ρ : Env Val} {Γ : Env Ty} : Type := *)
(*   { *)
(*     env_dom_match : env_dom_eq Γ ρ; *)
(*     env_val_models : forall x τ, *)
(*         Γ x = Some τ -> *)
(*         {v : Val & ρ x = Some v & R v τ} *)
(*   }. *)

Reserved Notation "'TCV' ⊢ v : τ" (at level 70, v at level 99, no associativity).
Reserved Notation "'ENV' ρ ⊨ Γ" (at level 69, no associativity).
Inductive tc_val : Val -> Ty -> Type :=
| TCVReal (r : R)
  : (TCV ⊢ v_real r : ℝ)
| TCVClo {x : Var} {body : Expr} {Γ_clo : Env Ty} {τa τr : Ty} {ρ_clo : Env Val}
  : (ENV ρ_clo ⊨ Γ_clo) ->
    (TC (extend Γ_clo x τa) ⊢ body : τr) ->
    (TCV ⊢ v_clo x body ρ_clo : (τa ~> τr))
with
tc_env : Env Val -> Env Ty -> Type :=
| TCEnv {Γ ρ} :
    env_dom_eq Γ ρ ->
    (forall x τ v,
        Γ x = Some τ ->
        ρ x = Some v ->
        tc_val v τ) ->
    tc_env ρ Γ
where "'TCV' ⊢ v : τ" := (tc_val v τ)
and "'ENV' ρ ⊨ Γ" := (tc_env ρ Γ).

Scheme tc_val_env_rect := Induction for tc_val Sort Type
with
tc_env_val_rect := Induction for tc_env Sort Type.

Lemma lookup_WT_Val {Γ ρ} (Hρ : ENV ρ ⊨ Γ) {x τ v} :
  Γ x = Some τ ->
  ρ x = Some v ->
  {v : Val | inhabited (TCV ⊢ v : τ)}.
Proof.
  intros.
  exists v.
  inversion Hρ.
  subst.
  constructor.
  eapply X; eauto.
Qed.

Definition Entropy := nat -> {r : R | 0 <= r <= 1}.

Definition πL (σ : Entropy) : Entropy := fun n => σ (2 * n)%nat.
Definition πR (σ : Entropy) : Entropy := fun n => σ (2 * n + 1)%nat.

Fixpoint π (n : nat) (σ : Entropy) : Entropy :=
  match n with
  | O => πL σ
  | S n' => π n' (πR σ)
  end.


Definition eval_a ρ (e : AExpr) : option Val :=
  match e with
  | e_real r => Some (v_real r)
  | e_lam x body => Some (v_clo x body ρ)
  | e_var x => ρ x
  end.

Reserved Notation "'EVAL' ρ , σ ⊢ e ⇓ v , w" (at level 69, e at level 99, no associativity).
Inductive eval (ρ : Env Val) (σ : Entropy) : forall (e : Expr) (v : Val) (w : R+), Type :=
| EPure (ae : AExpr) (v : Val) :
    eval_a ρ ae = Some v ->
    (EVAL ρ, σ ⊢ e_pure ae ⇓ v, nnr_1)
| EApp {e0 e1 : Expr} 
       {x : Var} {body : Expr} {ρ_clo : Env Val}
       {v1 v2 : Val}
       {w0 w1 w2 : R+}
  : (EVAL ρ, (π 0 σ) ⊢ e0 ⇓ v_clo x body ρ_clo, w0) ->
    (EVAL ρ, (π 1 σ) ⊢ e1 ⇓ v1, w1) ->
    (EVAL (extend ρ_clo x v1), (π 2 σ) ⊢ body ⇓ v2, w2) ->
    (EVAL ρ, σ ⊢ e_app e0 e1 ⇓ v2, w0 [*] w1 [*] w2)
| EFactor {e : Expr} {r : R} {w : R+} (rpos : 0 <= r)
  : (EVAL ρ, σ ⊢ e ⇓ v_real r, w) ->
    (EVAL ρ, σ ⊢ e_factor e ⇓ v_real r, mknnr r rpos [*] w)
| ESample
  : (EVAL ρ, σ ⊢ e_sample ⇓ v_real (proj1_sig (σ 0%nat)), nnr_1)
| EPlus {e0 e1 : Expr} {r0 r1 : R} {w0 w1 : R+}
  : (EVAL ρ, (π 0 σ) ⊢ e0 ⇓ v_real r0, w0) ->
    (EVAL ρ, (π 1 σ) ⊢ e1 ⇓ v_real r1, w1) ->
    (EVAL ρ, σ ⊢ e_plus e0 e1 ⇓ v_real (r0 + r1), w0 [*] w1)
where "'EVAL' ρ , σ ⊢ e ⇓ v , w" := (eval ρ σ e v w)
.

Record Config τ := mk_config
  { config_Γ : Env Ty;
    config_ρ : Env Val;
    config_Hρ : ENV config_ρ ⊨ config_Γ;
    config_e : Expr;
    config_He : (TC config_Γ ⊢ config_e : τ);
  }.

Arguments mk_config {_ _ _} _ {_} _.

Lemma env_model_extend
      {ρ Γ} (Hρ : ENV ρ ⊨ Γ) x {v τ} (Hv : (TCV ⊢ v : τ))
  : ENV (extend ρ x v) ⊨ (extend Γ x τ).
Proof.
  unfold extend.
  constructor. {
    constructor. {
      destruct Var_eq_dec; intros H. {
        inversion H.
      } {
        inversion Hρ; subst.
        rewrite <- (H0 x).
        auto.
      }
    } {
      destruct Var_eq_dec; intros H. {
        inversion H.
      } {
        inversion Hρ; subst.
        rewrite (H0 x).
        auto.
      }
    }
  } {
    intros.
    destruct Var_eq_dec. {
      inversion H.
      inversion H0.
      subst.
      auto.
    } {
      inversion Hρ; subst.
      eapply X; eauto.
    }
  }
Qed.

Lemma ty_eq_dec : forall (τ τ' : Ty),
    {τ = τ'} + {τ <> τ'}.
Proof.
  decide equality.
Defined.

Axiom decidable_tc : forall Γ e,
    ({τ : Ty & TC Γ ⊢ e : τ}) + (~exists τ, inhabited (TC Γ ⊢ e : τ)).

Axiom decidable_vtc : forall v τ,
    (TCV ⊢ v : τ) + (~inhabited (TCV ⊢ v : τ)).
