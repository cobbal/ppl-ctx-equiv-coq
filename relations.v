Require Import Basics.
Require Import Reals.

Local Open Scope R.

Parameter Var : Type.
Parameter Var_eq_dec : forall x y : Var, {x = y} + {x <> y}.

Inductive Ty :=
| ℝ : Ty
| Arrow : Ty -> Ty -> Ty
.
Notation "x ~> y" := (Arrow x y) (at level 69, right associativity, y at level 70).

Inductive Expr :=
| e_real : R -> Expr
| e_var : Var -> Expr
| e_lam : Var -> Ty -> Expr -> Expr
| e_app : Expr -> Expr -> Expr
| e_plus : Expr -> Expr -> Expr
| e_sample : Expr
| e_factor : Expr -> Expr
.

Notation "` x" := (e_var x) (at level 69).
Notation "'λ' x ; τ , e" := (e_lam x τ e) (at level 69, right associativity).
Notation "e0 @ e1" := (e_app e0 e1) (at level 68, left associativity).

Definition Env (T : Type) := Var -> option T.
Definition empty_env {T : Type} : Env T := const None.
Definition extend {T} (ρ : Env T) (x : Var) (v : T) : Env T :=
  fun y => if Var_eq_dec x y then Some v else ρ x.

Reserved Notation "'TC' Γ ⊢ e : τ" (at level 70, e at level 99, no associativity).
Inductive tc (Γ : Env Ty) : Expr -> Ty -> Prop :=
| TCReal (r : R)
  : TC Γ ⊢ e_real r : ℝ
| TCVar (x : Var) (τ : Ty)
  : Γ x = Some τ ->
    TC Γ ⊢ `x : τ
| TCLam (x : Var) (τa τr : Ty) (body : Expr)
  : (TC (extend Γ x τa) ⊢ body : τr) ->
    TC Γ ⊢ λ x ; τa , body : τa ~> τr
| TCApp (e0 e1 : Expr) (τa τr : Ty)
  : (TC Γ ⊢ e0 : τa ~> τr) ->
    (TC Γ ⊢ e1 : τa) ->
    TC Γ ⊢ e0 @ e1 : τr
| TCPlus (e0 e1 : Expr)
  : (TC Γ ⊢ e0 : ℝ) ->
    (TC Γ ⊢ e1 : ℝ) ->
    (TC Γ ⊢ e_plus e0 e1 : ℝ)
| TCSample
  : TC Γ ⊢ e_sample : ℝ
| TCFactor (e : Expr)
  : (TC Γ ⊢ e : ℝ) ->
    TC Γ ⊢ e_factor e : ℝ
where "'TC' Γ ⊢ e : τ" := (tc Γ e τ)
.

Inductive Val :=
| v_r : R -> Val
| v_clo : Var -> Expr -> Env (Val * Ty) -> Val.

Definition Entropy := nat -> {r : R | 0 <= r /\ r <= 1}.

Program Definition join (σ0 σ1 : Entropy) : Entropy :=
  fun n =>
    if Even.even_odd_dec n
    then σ0 (Nat.div2 n)
    else σ1 (Nat.div2 n).

Reserved Notation "'EVAL' ρ , σ ⊢ e ⇓ v , w" (at level 69, e at level 99, no associativity).
Inductive eval (ρ : Env (Val * Ty)) : Entropy -> Expr -> Val -> R -> Type :=
| EVar (σ : Entropy) (x : Var) (v : Val) (τ : Ty)
  : ρ x = Some (v, τ) ->
    EVAL ρ, σ ⊢ `x ⇓ v, 1
| EConst (σ : Entropy) (r : R)
  : EVAL ρ, σ ⊢ e_real r ⇓ v_r r, 1
| ELam (σ : Entropy) (x : Var) (τ : Ty) (e : Expr)
  : EVAL ρ, σ ⊢ λ x ; τ , e ⇓ v_clo x e ρ, 1
| EPlus (σ0 σ1 : Entropy) (e0 e1 : Expr) (r0 r1 : R) (w0 w1 : R)
  : (EVAL ρ, σ0 ⊢ e0 ⇓ v_r r0, w0) ->
    (EVAL ρ, σ1 ⊢ e1 ⇓ v_r r1, w1) ->
    EVAL ρ, (join σ0 σ1) ⊢ e_plus e0 e1 ⇓ v_r (r0 + r1), w0 * w1
| EApp (σ0 σ1 σ2 : Entropy) (e0 e1 : Expr)
       (x : Var) (body : Expr) (ρ_clo : Env (Val * Ty))
       (v1 v2 : Val)
       (w0 w1 w2 : R)
  : EVAL ρ, σ0 ⊢ e0 ⇓ v_clo x body ρ_clo, w0 ->
    EVAL ρ, σ1 ⊢ e1 ⇓ v1, w1 ->
    EVAL ρ_clo, σ2 ⊢ body ⇓ v2, w2 ->
    EVAL ρ, (join σ0 (join σ1 σ2)) ⊢ e0 @ e1 ⇓ v2, w0 * w1 * w2
| ESample (σ : Entropy)
  : EVAL ρ, σ ⊢ e_sample ⇓ v_r (proj1_sig (σ 0%nat)), 1
| EFactor (σ : Entropy) (e : Expr) (r w : R)
  : r > 0 ->
    EVAL ρ, σ ⊢ e ⇓ v_r r, w ->
    EVAL ρ, σ ⊢ e_factor e ⇓ v_r r, r * w
where "'EVAL' ρ , σ ⊢ e ⇓ v , w" := (eval ρ σ e v w)
.

Definition Config := (Env (Val * Ty) * Expr)%type.

Definition Event := Val -> Prop.

Axiom μ : forall τ : Ty, Env (Val * Ty) -> Expr -> Event -> R.

























Definition A_rel' (V_rel : Ty -> Val -> Val -> Type) (τ : Ty) (A : Event) :=
  forall v0 v1,
    V_rel τ v0 v1 ->
    (A v0 <-> A v1).

Definition E_rel' (V_rel : Ty -> Val -> Val -> Type) (τ : Ty) (c0 c1 : Config) :=
  let (ρ0, e0) := c0 in
  let (ρ1, e1) := c1 in
  forall A, A_rel' V_rel τ A ->
            μ τ ρ0 e0 A = μ τ ρ1 e1 A.

Fixpoint V_rel τ v0 v1 : Type :=
  match τ with
  | ℝ => match v0, v1 with
         | v_r r0, v_r r1 => r0 = r1
         | _, _ => False
         end
  | τ0 ~> τ1 => match v0, v1 with
                | v_clo x0 e0 ρ0, v_clo x1 e1 ρ1 =>
                  V_rel τ0 v0 v1 ->
                  E_rel' V_rel τ1
                       (extend ρ0 x0 (v0, τ0), e0)
                       (extend ρ1 x1 (v1, τ1), e1)
                | _, _ => False
                end
  end
.
Definition E_rel := E_rel' V_rel.

Fixpoint val_models (τ : Ty) (v : Val) : Prop :=
  match τ, v with
  | ℝ, v_r _ => True
  | τa ~> τr, v_clo x e ρ => True (* Well, what should it be? *)
  | _, _ => False
  end.
Notation "'VAL' τ ⊨ v" := (val_models τ v) (at level 69, no associativity).

Definition env_models (Γ : Env Ty) (ρ : Env (Val * Ty)) :=
  forall x τ,
    Γ x = Some τ ->
    {v | ρ x = Some (v, τ) /\ VAL τ ⊨ v}.
Notation "'ENV' Γ ⊨ ρ" := (env_models Γ ρ) (at level 69, no associativity).

Definition G_rel (Γ : Env Ty) (ρ0 ρ1 : Env (Val * Ty)) : Type :=
  forall x τ
         (Γ_models_ρ0 : ENV Γ ⊨ ρ0)
         (Γ_models_ρ1 : ENV Γ ⊨ ρ1)
         (Γx_is_τ : Γ x = Some τ),
    V_rel τ
          (proj1_sig (Γ_models_ρ0 x τ Γx_is_τ))
          (proj1_sig (Γ_models_ρ1 x τ Γx_is_τ)).

(* this won't be true without a real definition of contexts *)
Definition obs_equiv (e1 e2 : Expr) :=
  forall (C : Expr -> Expr) (A : Event),
    μ ℝ empty_env (C e1) A = μ ℝ empty_env (C e2) A.
Notation "e0 '=ctx' e1" := (obs_equiv e0 e1) (at level 60, no associativity).

Definition related_expr (Γ : Env Ty) (e0 e1 : Expr) (τ : Ty) :=
  forall ρ0 ρ1,
    G_rel Γ ρ0 ρ1 ->
    E_rel τ (ρ0, e0) (ρ1, e1).
Notation "'EXP' Γ ⊢ e0 ≈ e1 : τ" :=
  (related_expr Γ e0 e1 τ)
    (at level 69, e0 at level 99, e1 at level 99, no associativity).