Require Import Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import utils.
Require Import List.

Parameter Var : Type. (* := nat. *)
Parameter Var_eq_dec : forall x y : Var, {x = y} + {x <> y}.  (* := Nat.eq_dec. *)
Parameter fresh_Var : list Var -> Var.

Inductive Ty :=
| ℝ : Ty
| Arrow : Ty -> Ty -> Ty
.
Notation "x ~> y" := (Arrow x y) (at level 69, right associativity, y at level 70).

Lemma ty_eq_dec : forall (τ τ' : Ty), {τ = τ'} + {τ <> τ'}.
Proof.
  decide equality.
Defined.

Definition Env (T : Type) := Var -> option T.
Definition empty_env {T : Type} : Env T := fun x => None.
Notation "·" := empty_env.
Definition extend {T} (ρ : Env T) (x : Var) (v : T) : Env T :=
  fun x' => if Var_eq_dec x x' then Some v else ρ x'.

Inductive Expr :=
| e_app : Expr -> Expr -> Expr
| e_factor : Expr -> Expr
| e_sample : Expr
| e_plus : Expr -> Expr -> Expr
| e_pure : Val -> Expr
with Val :=
| e_real : R -> Val
| e_lam : Var -> Ty -> Expr -> Val
| e_var : Var -> Val
.

Scheme Expr_Val_rect := Induction for Expr Sort Type
with
Val_Expr_rect := Induction for Val Sort Type.

Fixpoint depth_of (e : Expr) : nat :=
  match e with
  | e_app e0 e1 => S (max (depth_of e0) (depth_of e1))
  | e_factor e0 => S (depth_of e0)
  | e_sample => O
  | e_plus e0 e1 => S (max (depth_of e0) (depth_of e1))
  | e_pure (e_real _) => O
  | e_pure (e_var x) => O
  | e_pure (e_lam x τa body) => S (depth_of body)
  end.

Fixpoint vars_of (e : Expr) : list Var :=
  match e with
  | e_app e0 e1 => vars_of e0 ++ vars_of e1
  | e_factor e0 => vars_of e0
  | e_sample => nil
  | e_plus e0 e1 => vars_of e0 ++ vars_of e1
  | e_pure (e_real _) => nil
  | e_pure (e_var x) => x :: nil
  | e_pure (e_lam x τa body) => x :: vars_of body
  end.
























Require Import Reals.
Require Import List.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import nnr.
Require Import utils.
Require Import List.


Local Open Scope R.

Parameter Var : Type. (* := nat. *)
Parameter Var_eq_dec : forall x y : Var, {x = y} + {x <> y}.  (* := Nat.eq_dec. *)
Parameter fresh_Var : list Var -> Var.
Parameter fresh_Var_fresh : forall l, ~ (List.In (fresh_Var l) l).

Inductive Ty :=
| ℝ : Ty
| Arrow : Ty -> Ty -> Ty
.
Notation "x ~> y" := (Arrow x y) (at level 69, right associativity, y at level 70).

Lemma ty_eq_dec : forall (τ τ' : Ty), {τ = τ'} + {τ <> τ'}.
Proof.
  decide equality.
Defined.

Inductive Expr :=
| e_app : Expr -> Expr -> Expr
| e_factor : Expr -> Expr
| e_sample : Expr
| e_plus : Expr -> Expr -> Expr
| e_pure : Val -> Expr
with Val :=
| e_real : R -> Val
| e_lam : Var -> Ty -> Expr -> Val
| e_var : Var -> Val
.

Scheme Expr_Val_rect := Induction for Expr Sort Type
with
Val_Expr_rect := Induction for Val Sort Type.

(* capture avoiding substitution modeled after
   https://calculist.blogspot.com/2007/05/capture-avoiding-substitution-in-plt.html *)

Fixpoint depth_of (e : Expr) : nat :=
  match e with
  | e_app e0 e1 => S (max (depth_of e0) (depth_of e1))
  | e_factor e0 => S (depth_of e0)
  | e_sample => O
  | e_plus e0 e1 => S (max (depth_of e0) (depth_of e1))
  | e_pure (e_real _) => O
  | e_pure (e_var x) => O
  | e_pure (e_lam x τa body) => S (depth_of body)
  end.

Fixpoint vars_of (e : Expr) : list Var :=
  match e with
  | e_app e0 e1 => vars_of e0 ++ vars_of e1
  | e_factor e0 => vars_of e0
  | e_sample => nil
  | e_plus e0 e1 => vars_of e0 ++ vars_of e1
  | e_pure (e_real _) => nil
  | e_pure (e_var x) => x :: nil
  | e_pure (e_lam x τa body) => x :: vars_of body
  end.

Fixpoint chvar (x y : Var) (e : Expr) : Expr :=
  match e with
  | e_app e0 e1 => e_app (chvar x y e0) (chvar x y e1)
  | e_factor e0 => e_factor (chvar x y e0)
  | e_sample => e_sample
  | e_plus e0 e1 => e_plus (chvar x y e0) (chvar x y e1)
  | e_pure (e_real r) => e_pure (e_real r)
  | e_pure (e_var x') =>
    if Var_eq_dec x x'
    then e_pure (e_var y)
    else e_pure (e_var x')
  | e_pure (e_lam x' τa body) =>
    if Var_eq_dec x x'
    then e_pure (e_lam x' τa body)
    else e_pure (e_lam x' τa (chvar x y body))
  end.

Require Coq.Program.Wf.
Require Import Lia.
Require Import Omega.

Lemma chvar_depth_invariant e x y : depth_of e = depth_of (chvar x y e).
Proof.
  induction e using Expr_Val_rect
  with (P0 := fun v : Val => depth_of (e_pure v) = depth_of (chvar x y (e_pure v)));
simpl;
try rewrite IHe1;
try rewrite IHe2;
try destruct Var_eq_dec;
simpl;
auto.
Qed.

(* Coq.Program.Wf was giving giant, slow programs; need to do this myself *)
Program Fixpoint subst_val_n
        (x : Var) (v : Val)
        (n : nat) (e : Expr) (pf : (depth_of e <= n)%nat)
  : Expr :=
  match n, e with
  | S n', e_app e0 e1 => e_app (subst_val_n x v n' e0 _) (subst_val_n x v n' e1 _)
  | S n', e_factor e0 => e_factor (subst_val_n x v n' e0 _)
  | _, e_sample => e_sample
  | S n', e_plus e0 e1 => e_plus (subst_val_n x v n' e0 _) (subst_val_n x v n' e1 _)
  | _, e_pure (e_real r) => e_pure (e_real r)
  | _, e_pure (e_var x') =>
    if Var_eq_dec x x'
    then e_pure v
    else e_pure (e_var x')
  | S n', e_pure (e_lam x' τa body) =>
    if Var_eq_dec x x'
    then e_pure (e_lam x' τa body)
    else
      let x_new := fresh_Var (vars_of body ++ vars_of (e_pure v)) in
      e_pure (e_lam x_new τa (subst_val_n x v n' (chvar x' x_new body) _))

  | O, e_app _ _
  | O, e_factor _
  | O, e_plus _ _
  | O, e_pure (e_lam _ _ _)
    => False_rect _ _
  end.