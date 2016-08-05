Require Import Basics.
Require Import Reals.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.

Local Open Scope R.

Parameter Var : Type.
Parameter Var_eq_dec : forall x y : Var, {x = y} + {x <> y}.

Inductive Ty :=
| ℝ : Ty
| Arrow : Ty -> Ty -> Ty
| Prod : Ty -> Ty -> Ty
.
Notation "x ~> y" := (Arrow x y) (at level 69, right associativity, y at level 70).
Notation "x ⨉ y" := (Prod x y) (at level 70).

Inductive Expr :=
| e_let : Var -> CExpr -> Expr -> Expr
| EC : CExpr -> Expr
| EA : AExpr -> Expr
with AExpr :=
| e_real : R -> AExpr
| e_var : Var -> AExpr
| e_lam : Var -> Ty -> Expr -> AExpr
with CExpr :=
| e_app : AExpr -> AExpr -> CExpr
| e_factor : AExpr -> CExpr
| e_sample : CExpr
| e_plus : AExpr -> AExpr -> CExpr
.

(* Scheme expr_eac_rec := Induction for Expr Sort Prop *)
(* with expr_ace_rec := Induction for AExpr Sort Prop *)
(* with expr_cea_rec := Induction for CExpr Sort Prop. *)

Notation "` x" := (e_var x) (at level 69).
Notation "'λ' x ; τ , e" := (e_lam x τ e) (at level 69, right associativity).
Notation "e0 @ e1" := (e_app e0 e1) (at level 68, left associativity).

Definition Env (T : Type) := Var -> option T.
Definition empty_env {T : Type} : Env T := const None.
Definition extend {T} (ρ : Env T) (x : Var) (v : T) : Env T :=
  fun y => if Var_eq_dec x y then Some v else ρ x.
Notation "ρ [ x → v ]" := (extend ρ x v) (at level 68, left associativity).

Reserved Notation "'TC' Γ ⊢ e : τ" (at level 70, e at level 99, no associativity).
Reserved Notation "'TC_A' Γ ⊢ e : τ" (at level 70, e at level 99, no associativity).
Reserved Notation "'TC_C' Γ ⊢ e : τ" (at level 70, e at level 99, no associativity).
Inductive tc {Γ : Env Ty} : Expr -> Ty -> Prop :=
| TCLet (x : Var) (e0 : CExpr) (e1 : Expr) (τ0 τ1 : Ty)
  : (TC Γ ⊢ EC e0 : τ0) ->
    (TC (Γ[x → τ0]) ⊢ e1 : τ1) ->
    TC Γ ⊢ e_let x e0 e1 : τ1

| TCReal (r : R)
  : TC_A Γ ⊢ e_real r : ℝ
| TCVar (x : Var) (τ : Ty)
  : Γ x = Some τ ->
    TC_A Γ ⊢ `x : τ
| TCLam (x : Var) (τa τr : Ty) (body : Expr)
  : (TC (extend Γ x τa) ⊢ body : τr) ->
    TC_A Γ ⊢ λ x ; τa , body : τa ~> τr

| TCApp (e0 e1 : AExpr) (τa τr : Ty)
  : (TC_A Γ ⊢ e0 : τa ~> τr) ->
    (TC_A Γ ⊢ e1 : τa) ->
    TC_C Γ ⊢ e0 @ e1 : τr
| TCPlus (e0 e1 : AExpr)
  : (TC_A Γ ⊢ e0 : ℝ) ->
    (TC_A Γ ⊢ e1 : ℝ) ->
    (TC_C Γ ⊢ e_plus e0 e1 : ℝ)
| TCSample
  : TC_C Γ ⊢ e_sample : ℝ
| TCFactor (e : AExpr)
  : (TC_A Γ ⊢ e : ℝ) ->
    TC_C Γ ⊢ e_factor e : ℝ
where "'TC' Γ ⊢ e : τ" := (tc (Γ := Γ) e τ)
and "'TC_A' Γ ⊢ e : τ" := (tc (Γ := Γ) (EA e) τ)
and "'TC_C' Γ ⊢ e : τ" := (tc (Γ := Γ) (EC e) τ).

Inductive Val :=
| v_real : R -> Val
| v_clo : Var -> Expr -> Env Val -> Val
| v_pair : Val -> Val -> Val.

Definition Entropy := nat -> {r : R | 0 <= r /\ r <= 1}.

Definition Ejoin (σ0 σ1 : Entropy) : Entropy :=
  fun n =>
    if Even.even_odd_dec n
    then σ0 (Nat.div2 n)
    else σ1 (Nat.div2 n).

Axiom Esplit : Entropy -> (Entropy * Entropy).
Axiom split_inv_join : forall σ1 σ2, Esplit (Ejoin σ1 σ2) = (σ1, σ2).
Axiom join_inv_split : forall σ, Ejoin (fst (Esplit σ)) (snd (Esplit σ)) = σ.

Definition πL (σ : Entropy) : Entropy := fst (Esplit σ).
Definition πR (σ : Entropy) : Entropy := snd (Esplit σ).

Reserved Notation "'EVAL_E' ρ , σ ⊢ e ⇓ v , w" (at level 69, e at level 99, no associativity).
Reserved Notation "'EVAL_A' ρ ⊢ e ⇓ v" (at level 69, e at level 99, no associativity).
Reserved Notation "'EVAL_C' ρ , σ ⊢ e ⇓ v , w" (at level 69, e at level 99, no associativity).
Inductive eval (ρ : Env Val) : Entropy -> Expr -> Val -> R -> Prop :=
| ELet (σ : Entropy) {x : Var} {e0 : CExpr} {e1 : Expr} {v0 v1 : Val} {w0 w1 : R}
  : (EVAL_C ρ, (πL σ) ⊢ e0 ⇓ v0, w0) ->
    (EVAL_E (ρ[x → v0]), (πR σ) ⊢ e1 ⇓ v1, w1) ->
    (EVAL_E ρ, σ ⊢ e_let x e0 e1 ⇓ v1, w0 * w1)
| EEA σ {e v}
  : (EVAL_A ρ ⊢ e ⇓ v) ->
    (EVAL_E ρ, σ ⊢ EA e ⇓ v, 1)
| EEC {σ e v w}
  : (EVAL_C ρ, σ ⊢ e ⇓ v, w) ->
    (EVAL_E ρ, σ ⊢ EC e ⇓ v, w)
with eval_a (ρ : Env Val) : AExpr -> Val -> Prop :=
| EVar {x : Var} {v : Val}
  : ρ x = Some v ->
    (EVAL_A ρ ⊢ `x ⇓ v)
| EReal (r : R)
  : (EVAL_A ρ ⊢ e_real r ⇓ v_real r)
| ELam (x : Var) (τ : Ty) (e : Expr)
  : (EVAL_A ρ ⊢ λ x ; τ , e ⇓ v_clo x e ρ)
with eval_c (ρ : Env Val) : Entropy -> CExpr -> Val -> R -> Prop :=
| EPlus (σ : Entropy) {e0 e1 : AExpr} {r0 r1 : R}
  : (EVAL_A ρ ⊢ e0 ⇓ v_real r0) ->
    (EVAL_A ρ ⊢ e1 ⇓ v_real r1) ->
    (EVAL_C ρ, σ ⊢ e_plus e0 e1 ⇓ v_real (r0 + r1), 1)
| EApp (σ : Entropy) {e0 e1 : AExpr}
       {x : Var} {body : Expr} {ρ_clo : Env Val}
       {v1 v2 : Val} {w : R}
  : (EVAL_A ρ ⊢ e0 ⇓ v_clo x body ρ_clo) ->
    (EVAL_A ρ ⊢ e1 ⇓ v1) ->
    (EVAL_E (ρ_clo[x → v1]), σ ⊢ body ⇓ v2, w) ->
    (EVAL_C ρ, σ ⊢ e0 @ e1 ⇓ v2, w)
| ESample (σ : Entropy)
  : (EVAL_C ρ, σ ⊢ e_sample ⇓ v_real (proj1_sig (σ 0%nat)), 1)
| EFactor (σ : Entropy) {e : AExpr} {r : R}
  : (EVAL_A ρ ⊢ e ⇓ v_real r) ->
    (EVAL_C ρ, σ ⊢ e_factor e ⇓ v_real r, r)
where "'EVAL_E' ρ , σ ⊢ e ⇓ v , w" := (@eval ρ σ e v w)
and "'EVAL_A' ρ ⊢ e ⇓ v" := (@eval_a ρ e v)
and "'EVAL_C' ρ , σ ⊢ e ⇓ v , w" := (@eval_c ρ σ e v w)
.

Definition Config := (Env Val * Expr)%type.

Definition Event X := X -> bool.

Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

Definition uniqueT {A : Type} (P : A -> Type) (x : A) :=
  (P x * forall x' : A, P x' -> x = x')%type.

Notation "'existsT' ! x .. y , p" :=
  (sigT (uniqueT (fun x => .. (sigT (uniqueT (fun y => p))) ..)))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' ! '/ ' x .. y , '/ ' p ']'")
    : type_scope.

Axiom eval_dec :
  forall ρ e σ,
    (existsT! vw : (Val * R), let (v, w) := vw in EVAL_E ρ, σ ⊢ e ⇓ v, w) +
    ((existsT vw : (Val * R), let (v, w) := vw in EVAL_E ρ, σ ⊢ e ⇓ v, w) -> False).

Print sigT.

Definition option0 : option R -> R :=
  fun o =>
    match o with
    | Some r => r
    | None => 0
    end.

Notation "f <$> x" := (option_map f x) (at level 20).
Definition option_ap {A B} (o_f : option (A -> B)) : option A -> option B :=
  fun a =>
    match o_f with
    | Some f => f <$> a
    | None => None
    end.
Notation "f <*> x" := (option_ap f x) (at level 20).

Definition ev ρ e σ : option Val :=
  match eval_dec ρ e σ with
  | inl (existT _ (v, w) _) => Some v
  | inr _ => None
  end.

Definition ew ρ e σ : R :=
  match eval_dec ρ e σ with
  | inl (existT _ (v, w) _) => w
  | inr _ => 0
  end.

Definition evalin ρ e (V : Event Val) σ : R :=
  match ev ρ e σ with
  | Some v => if V v then 1 else 0
  | None => 0
  end * ew ρ e σ.

Definition applyin (v v' : option Val) A σ :=
  match v, v' with
  | Some (v_clo x e ρ), Some v' => evalin (ρ[x → v']) e A σ
  | _, _ => 0
  end.

Record Meas {A} :=
  { Meas_fn : Event A -> R;
    (* axioms ... *)
  }.
Arguments Meas _ : clear implicits.

Axiom μEntropy : Meas Entropy.

Axiom Integration : forall {A}, (A -> R) -> Meas A -> R.
(* Notation "'∫' fx ';' μ ( 'd' x )" := (Integration (fun x => fx) μ). *)

Axiom Integration_linear :
  forall {A} (f : A -> R) (μ : Meas A) (c : R),
    c * Integration f μ = Integration (fun x => c * f x) μ.

Axiom int_const_entropy :
  forall (f : Entropy -> R)
         (v : R),
    (forall x, f x = v) ->
    Integration f μEntropy = v.

(* Axiom μ : forall τ : Ty, Env Val -> Expr -> Event -> R. *)
Definition μ ρ e V :=
  Integration (fun σ => evalin ρ e V σ) μEntropy.

Definition A_rel (V_rel : Ty -> Val -> Val -> Type) (τ : Ty) (A : Event Val) :=
  forall v0 v1,
    V_rel τ v0 v1 ->
    (A v0 = A v1).

Definition E_rel (V_rel : Ty -> Val -> Val -> Prop) (τ : Ty) (c0 c1 : Config) : Prop :=
  let (ρ0, e0) := c0 in
  let (ρ1, e1) := c1 in
  forall A, A_rel V_rel τ A ->
            μ ρ0 e0 A = μ ρ1 e1 A.

Definition EA_rel (V_rel : Ty -> Val -> Val -> Prop) (τ : Ty) (c0 c1 : Env Val * AExpr) : Prop :=
  let (ρ0, e0) := c0 in
  let (ρ1, e1) := c1 in
  exists vs : Val * Val,
    V_rel τ (fst vs) (snd vs) /\
    EVAL_A ρ0 ⊢ e0 ⇓ (fst vs) /\
    EVAL_A ρ1 ⊢ e1 ⇓ (snd vs).

Reserved Notation "'VREL' v0 , v1 ∈ V[ τ ]"
         (at level 69, v0 at level 99, v1 at level 99, τ at level 99).
Fixpoint V_rel τ v0 v1 : Prop :=
  match τ with
  | ℝ => match v0, v1 with
         | v_real r0, v_real r1 => r0 = r1
         | _, _ => False
         end
  | τa ~> τr => match v0, v1 with
                | v_clo x0 e0 ρ0, v_clo x1 e1 ρ1 =>
                  forall {va0 va1},
                    V_rel τa va0 va1 ->
                    E_rel V_rel τr
                           (ρ0[x0 → va0], e0)
                           (ρ1[x1 → va1], e1)
                | _, _ => False
                end
  | τl ⨉ τr => match v0, v1 with
               | v_pair vl0 vr0, v_pair vl1 vr1 =>
                 V_rel τl vl0 vl1 /\ V_rel τr vr0 vr1
               | _, _ => False
               end
  end
where "'VREL' v0 , v1 ∈ V[ τ ]" := (V_rel τ v0 v1)
.
Notation "'EREL' e0 , e1 ∈ E[ τ ]" :=
  (E_rel V_rel τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, τ at level 99).
Notation "'EAREL' e0 , e1 ∈ E[ τ ]" :=
  (EA_rel V_rel τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, τ at level 99).
Notation "'AREL' v0 , v1 ∈ E[ τ ]" :=
  (A_rel V_rel τ v0 v1)
    (at level 69, v0 at level 99, v1 at level 99, τ at level 99).

Definition env_dom_eq {A B} (envA : Env A) (envB : Env B) :=
  forall x, envA x = None <-> envB x = None.
Record env_models {Γ : Env Ty} {ρ : Env Val} : Type :=
  {
    env_dom_match : env_dom_eq Γ ρ;
    env_val_models : forall x τ,
        Γ x = Some τ ->
        {v | ρ x = Some v}
  }.
Notation "'ENV' Γ ⊨ ρ" := (@env_models Γ ρ) (at level 69, no associativity).

(* record G_rel (Γ : env ty) (ρ : env val) : Type := *)
(*   (dom_match : ∀ x, lookup Γ x = none ↔ lookup ρ x = none) *)
(*   (values : Π x τ v, *)
(*     Π (Γx_eq : lookup Γ x = some τ) *)
(*       (ρx_eq : lookup ρ x = some v), *)
(*       V_rel τ v) *)

Record G_rel {Γ : Env Ty} {ρ0 ρ1 : Env Val}: Type :=
  {
    G_rel_modeling0 : ENV Γ ⊨ ρ0;
    G_rel_modeling1 : ENV Γ ⊨ ρ1;
    G_rel_V : forall {x v0 v1 τ},
                     Γ x = Some τ ->
                     ρ0 x = Some v0 ->
                     ρ1 x = Some v1 ->
        V_rel τ v0 v1
  }.
Arguments G_rel _ _ _ : clear implicits.
Notation "'GREL' ρ0 , ρ1 ∈ G[ Γ ]" :=
  (G_rel Γ ρ0 ρ1)
    (at level 69, ρ0 at level 99, ρ1 at level 99, Γ at level 99).

Definition related_exprs (Γ : Env Ty) (τ : Ty) (e0 e1 : Expr) : Prop :=
  (TC Γ ⊢ e0 : τ) /\
  (TC Γ ⊢ e1 : τ) /\
  forall ρ0 ρ1,
    GREL ρ0, ρ1 ∈ G[Γ] ->
    EREL (ρ0, e0), (ρ1, e1) ∈ E[τ].
Notation "'EXP' Γ ⊢ e0 ≈ e1 : τ" :=
  (related_exprs Γ τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, no associativity).
Definition related_aexprs (Γ : Env Ty) (τ : Ty) (e0 e1 : AExpr) :=
  (TC_A Γ ⊢ e0 : τ) /\
  (TC_A Γ ⊢ e1 : τ) /\
  forall ρ0 ρ1,
    GREL ρ0, ρ1 ∈ G[Γ] ->
    EAREL (ρ0, e0), (ρ1, e1) ∈ E[τ].
Notation "'AEXP' Γ ⊢ e0 ≈ e1 : τ" :=
  (related_aexprs Γ τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, no associativity).

(* this won't be true without a real definition of contexts *)
Definition obs_equiv (e1 e2 : Expr) :=
  forall (C : Expr -> Expr) (A : Event Val),
    μ empty_env (C e1) A = μ empty_env (C e2) A.
Notation "e0 '=ctx' e1" := (obs_equiv e0 e1) (at level 60, no associativity).

Ltac split3 := split; [|split].
(* absurdly common typo I'm sick of correcting *)
Ltac inductino a := induction a.

Ltac decide_eval' ρ v w e u :=
  let not_ex := fresh "not_ex" in
  destruct (eval_dec ρ) as [[[v w] [e u]] | not_ex];
  [| try (contradict not_ex; eexists (_, _); repeat constructor; eassumption)].
Tactic Notation "decide_eval" constr(ρ) "as"
       "[" ident(v) ident(w) ident(e) ident(u) "]"
  := (decide_eval' ρ v w e u).

Ltac congruence_μ := unfold μ; apply f_equal2; [extensionality σ | tauto].

Lemma compat_real Γ r :
  AEXP Γ ⊢ e_real r ≈ e_real r : ℝ.
Proof.
  repeat constructor.
  intros.
  exists (v_real r, v_real r); simpl.
  split3; auto; apply EReal.
Qed.

Lemma compat_ea_real Γ r :
  EXP Γ ⊢ EA (e_real r) ≈ EA (e_real r) : ℝ.
Proof.
  repeat constructor; intros; auto.
  intros A HA.

  congruence_μ.

  unfold evalin, ew, ev.
  decide_eval ρ0 as [v0 w0 ex0 u0].
  decide_eval ρ1 as [v1 w1 ex1 u1].

  inversion ex0.
  inversion ex1.
  inversion H1.
  inversion H6.
  subst.

  auto.
Qed.

Lemma compat_var Γ x τ :
  Γ x = Some τ ->
  AEXP Γ ⊢ `x ≈ `x : τ.
Proof.
  repeat constructor; intros; auto.

  induction (env_val_models (G_rel_modeling0 X) x τ H) as [v0 Hv0].
  induction (env_val_models (G_rel_modeling1 X) x τ H) as [v1 Hv1].
  pose proof (G_rel_V X) H Hv0 Hv1.

  exists (v0, v1).
  simpl.
  repeat constructor; auto.
Qed.

Lemma compat_ea_var Γ x τ :
  Γ x = Some τ ->
  EXP Γ ⊢ EA (`x) ≈ EA (`x) : τ.
Proof.
  repeat constructor; intros; auto.

  induction (env_val_models (G_rel_modeling0 X) x τ H) as [v0 Hv0].
  induction (env_val_models (G_rel_modeling1 X) x τ H) as [v1 Hv1].
  pose proof (G_rel_V X) H Hv0 Hv1.

  intros A HA.

  congruence_μ.

  unfold evalin, ev, ew.
  pose proof EEA _ σ (EVar _ Hv0) as E0.
  pose proof EEA _ σ (EVar _ Hv1) as E1.

  decide_eval ρ0 as [ve0 w0 ex0 u0].
  decide_eval ρ1 as [ve1 w1 ex1 u1].

  injection (u0 (_, _) E0); intros.
  injection (u1 (_, _) E1); intros.
  subst.
  replace (A v1) with (A v0); auto.
Qed.


Lemma extend_grel {Γ x ρ0 ρ1 v0 v1 τ} :
  (GREL ρ0, ρ1 ∈ G[Γ]) ->
  (VREL v0, v1 ∈ V[τ]) ->
  (GREL ρ0 [x → v0], ρ1 [x → v1] ∈ G[Γ[x → τ]]).
Proof.
  split; try split; intro x';
  unfold extend;
induction Var_eq_dec;
try (split; intro stupid; inversion stupid; fail);
try apply X;
try (eexists; trivial).

  intros.
  injection H0.
  injection H1.
  injection H2.
  intros.
  subst.
  auto.
Qed.

Lemma compat_lam Γ x body0 body1 τa τr :
  (EXP Γ[x → τa] ⊢ body0 ≈ body1 : τr) ->
  (AEXP Γ ⊢ λ x ; τa, body0 ≈ λ x ; τa, body1 : (τa ~> τr)).
Proof.
  intros.
  destruct H as [tc0 [tc1 H]].
  repeat constructor; auto.

  intros.
  exists (v_clo x body0 ρ0, v_clo x body1 ρ1).

  split3; simpl; try constructor.
  intros.

  apply H; auto.
  apply extend_grel; auto.
Qed.

Lemma compat_ea_lam Γ x body0 body1 τa τr :
  (EXP Γ[x → τa] ⊢ body0 ≈ body1 : τr) ->
  (EXP Γ ⊢ EA (λ x ; τa, body0) ≈ EA (λ x ; τa, body1) : (τa ~> τr)).
Proof.
  intros.
  destruct H as [TC0 [TC1 H]].
  split3; try (apply TCLam; assumption).
  intros.
  intros A HA.

  congruence_μ.

  pose proof EEA _ σ (ELam ρ0 x τa body0) as E0.
  pose proof EEA _ σ (ELam ρ1 x τa body1) as E1.

  unfold evalin, ev, ew.
  decide_eval ρ0 as [v0 w0 ex0 u0].
  decide_eval ρ1 as [v1 w1 ex1 u1].

  injection (u0 (_, _) E0); intros tH0a tH0b.
  injection (u1 (_, _) E1); intros tH1a tH1b.
  rewrite tH0a, tH0b, tH1a, tH1b in *.
  clear tH0a tH0b tH1a tH1b w0 v0 w1 v1 u0 u1 ex0 ex1.
  replace (A (v_clo x body1 ρ1)) with (A (v_clo x body0 ρ0)); [reflexivity|].

  apply HA.
  simpl.
  intros.
  apply H; auto.
  apply extend_grel; auto.
Qed.

Axiom lemma_9 : forall (g : Entropy -> Entropy -> R),
    Integration (fun σ => g (πL σ) (πR σ)) μEntropy =
    Integration (fun σ2 => Integration (fun σ1 => g σ1 σ2) μEntropy) μEntropy.

(* Lemma its_just_the_definition_of_applyin_how_hard_could_it_be : *)
(*   forall *)
(*   (ef ea : Expr) *)
(*   (ρ : Env Val) *)
(*   (A : Event Val), *)
(*     (fun σ => evalin ρ (ef @ ea) A σ) = *)
(*     (fun σ => applyin *)
(*                 (ev ρ ef (π 0 σ)) *)
(*                 (ev ρ ea (π 1 σ)) *)
(*                 A *)
(*                 (π 2 σ) *)
(*               * ew ρ ef (π 0 σ) *)
(*               * ew ρ ea (π 1 σ)). *)
(* Proof. *)
(*   intros. *)
(*   extensionality σ. *)
(*   unfold applyin, evalin, ev, ew. *)
(*   destruct (eval_dec ρ ef) as [[[vf rf] [Ef uf]] | not_ex]. { *)
(*     destruct (eval_dec ρ ea) as [[[va ra] [Ea ua]] | not_ex]. { *)
(*       destruct (eval_dec ρ (ef @ ea)) as [[[v r] [E u]] | not_ex]. { *)
(*         inversion E. *)
(*         pose proof uf (_, _) X as uf. *)
(*         pose proof ua (_, _) X0 as ua. *)
(*         inversion uf. *)
(*         inversion ua. *)
(*         rewrite H5, H6, H7, H8 in *. *)
(*         clear H5 H6 H7 H8 vf rf va ra. *)
(*         replace ((if A v then 1 else 0) * (w0 * w1 * w2)) *)
(*         with (((if A v then 1 else 0) * w2) * w0 * w1). { *)
(*           apply f_equal2; auto. *)
(*           apply f_equal2; auto. *)

(*           destruct eval_dec as [[[vr rr] [Er ur]] | not_ex]. { *)
(*             pose proof ur (_, _) X1. *)
(*             inversion H4. *)
(*             reflexivity. *)
(*           } { *)
(*             contradict not_ex. *)
(*             eexists (_, _). *)
(*             exact X1. *)
(*           } *)
(*         } { *)
(*           generalize (if A v then 1 else 0). *)
(*           intro. *)
(*           repeat rewrite Rmult_assoc. *)
(*           apply f_equal2; auto. *)
(*           rewrite <- Rmult_comm. *)
(*           rewrite Rmult_assoc. *)
(*           auto. *)
(*         } *)
(*       } { *)
(*         induction vf as [| x body ρ_clo|]. { *)
(*           repeat rewrite Rmult_0_l; auto. *)
(*         } { *)
(*           destruct eval_dec as [[[vr rr] [Er ur]] | not_ex2]. { *)
(*             contradict not_ex. *)
(*             eexists (_, _). *)
(*             eapply EApp. *)
(*             exact Ef. *)
(*             exact Ea. *)
(*             exact Er. *)
(*           } { *)
(*             repeat rewrite Rmult_0_l; auto. *)
(*           } *)
(*         } { *)
(*             repeat rewrite Rmult_0_l; auto. *)
(*         } *)
(*       } *)
(*     } { *)
(*       rewrite Rmult_0_r. *)
(*       destruct eval_dec as [[[vr rr] [Er ur]] | not_ex2]. { *)
(*         inversion Er. *)
(*         contradict not_ex. *)
(*         eexists (_, _). *)
(*         exact X0. *)
(*       } { *)
(*         rewrite Rmult_0_r; auto. *)
(*       } *)
(*     } *)
(*   } { *)
(*     repeat rewrite Rmult_0_l. *)
(*     destruct eval_dec as [[[vr rr] [Er ur]] | not_ex2]. { *)
(*       inversion Er. *)
(*       contradict not_ex. *)
(*       eexists (_, _). *)
(*       exact X. *)
(*     } { *)
(*       rewrite Rmult_0_r; auto. *)
(*     } *)
(*   } *)
(* Qed. *)

(* Definition ent_lift {A} (f : Entropy -> A) : Entropy -> Entropy -> A := *)
(*   fun σL σR => f (Ejoin σL σR). *)

(* Lemma ent_lift_same {A} (f : Entropy -> A) σ : *)
(*   ent_lift f (πL σ) (πR σ) = f σ. *)
(* Proof. *)
(*   unfold ent_lift, πL, πR. *)
(*   rewrite join_inv_split. *)
(*   auto. *)
(* Qed. *)

(* Lemma its_just_applying_lemma_9_how_hard_could_it_be : *)
(*   forall *)
(*   (ef ea : Expr) *)
(*   (ρ : Env Val) *)
(*   (A : Event Val), *)
(*     let f σ0 σ1 σ2 := *)
(*         applyin (ev ρ ef σ0) (ev ρ ea σ1) A σ2 *)
(*         * ew ρ ef σ0 *)
(*         * ew ρ ea σ1 *)
(*     in *)
(*     Integration (fun σ => f (π 0 σ) (π 1 σ) (π 2 σ)) μEntropy = *)
(*     Integration (fun σ2 => *)
(*     Integration (fun σ1 => *)
(*     Integration (fun σ0 => *)
(*                    f σ0 σ1 σ2 *)
(*                 ) μEntropy *)
(*                 ) μEntropy *)
(*                 ) μEntropy. *)
(* Proof. *)
(*   intros. *)

(*   assert *)
(*     (Integration (fun σ => f (π 0 σ) (π 1 σ) (π 2 σ)) μEntropy = *)
(*      Integration (fun σ3 => *)
(*      Integration (fun σ2 => *)
(*      Integration (fun σ1 => *)
(*      Integration (fun σ0 => *)
(*                     f σ0 σ1 σ2 *)
(*                  ) μEntropy *)
(*                  ) μEntropy *)
(*                  ) μEntropy *)
(*                  ) μEntropy). *)
(*   { *)
(*     simpl. *)
(*     repeat rewrite <- lemma_9. *)
(*     trivial. *)
(*   } { *)
(*     rewrite H. *)
(*     erewrite int_const_entropy. *)
(*     reflexivity. *)
(*     auto. *)
(*   } *)
(* Qed. *)

(* Definition meas_lift {A} (m : Meas A) : Meas (option A) := *)
(*   {| Meas_fn := fun p => Meas_fn m (fun a => p (Some a)) |}. *)

(* Axiom theorem_15 : *)
(*   forall (f : option Val -> R) {Γ e τ ρ}, *)
(*     (TC Γ ⊢ e : τ) -> *)
(*     (ENV Γ ⊨ ρ) -> *)
(*     Integration f (meas_lift {| Meas_fn := μ ρ e |}) = *)
(*     Integration (fun σ => f (ev ρ e σ) * ew ρ e σ) μEntropy. *)

(* Lemma its_just_applying_theorem_15_how_hard_could_it_be : *)
(*   forall *)
(*   {ef ea : Expr} *)
(*   Γ τa τr *)
(*   (tcf : TC Γ ⊢ ef : τa ~> τr) *)
(*   (tca : TC Γ ⊢ ea : τa) *)
(*   (ρ : Env Val) *)
(*   (env_models : ENV Γ ⊨ ρ) *)
(*   (A : Event Val), *)
(*     let f σ0 σ1 σ2 := *)
(*         applyin (ev ρ ef σ0) (ev ρ ea σ1) A σ2 *)
(*         * ew ρ ef σ0 *)
(*         * ew ρ ea σ1 *)
(*     in *)
(*     Integration (fun σ2 => *)
(*     Integration (fun σ1 => *)
(*     Integration (fun σ0 => *)
(*                    f σ0 σ1 σ2 *)
(*                 ) μEntropy *)
(*                 ) μEntropy *)
(*                 ) μEntropy = *)
(*     Integration (fun σ2 => *)
(*     Integration (fun va => *)
(*     Integration (fun vf => *)
(*                    applyin vf va A σ2 *)
(*                 ) (meas_lift {| Meas_fn := μ ρ ef |}) *)
(*                 ) (meas_lift {| Meas_fn := μ ρ ea |}) *)
(*                 ) μEntropy. *)
(* Proof. *)
(*   intros. *)
(*   apply f_equal2; auto. *)
(*   extensionality σ2. *)
(*   rewrite theorem_15 with (Γ := Γ) (τ := τa); auto. *)
(*   apply f_equal2; auto. *)
(*   extensionality σ1. *)
(*   rewrite theorem_15 with (Γ := Γ) (τ := τa ~> τr); auto. *)
(*   rewrite Rmult_comm. *)
(*   rewrite Integration_linear. *)
(*   apply f_equal2; auto. *)
(*   extensionality σ0. *)
(*   subst f. *)
(*   simpl. *)
(*   apply Rmult_comm. *)
(* Qed. *)

(* Definition preimage {A B R} (f : A -> B) : (B -> R) -> (A -> R) := *)
(*   fun eb a => eb (f a). *)

(* Definition ensemble_of_event {X} : Event X -> Ensemble X := *)
(*   fun A x => A x = true. *)

(* Axiom lemma_3 : *)
(*   forall {X} *)
(*          (M : Ensemble (Event X)) *)
(*          (μ1 μ2 : Meas X) *)
(*          (μs_aggree : forall A, M A -> *)
(*                                 Meas_fn μ1 A = Meas_fn μ2 A) *)
(*          (f : X -> R) *)
(*          (f_is_M_measurable : *)
(*             forall (B : R -> bool), *)
(*               M (preimage f B)), *)
(*     Integration f μ1 = Integration f μ2. *)

(* Axiom product_measure : forall {A B} (μA : Meas A) (μB : Meas B), Meas (A * B). *)
(* Axiom product_measure_integration : *)
(*   forall {A B} (μA : Meas A) (μB : Meas B) f, *)
(*     Integration (fun x => Integration (fun y => f x y) μB) μA = *)
(*     Integration (fun xy => f (fst xy) (snd xy)) (product_measure μA μB). *)

(* Axiom product_measure_eq_on_rectangles_is_eq : *)
(*   forall {A B} (μA0 μA1 : Meas A) (μB0 μB1 : Meas B), *)
(*     (forall (X : Event A) (Y : Event B), *)
(*         Meas_fn μA0 X * Meas_fn μB0 Y = Meas_fn μA1 X * Meas_fn μB1 Y) -> *)
(*     product_measure μA0 μB0 = *)
(*     product_measure μA1 μB1. *)


(* Definition rectangle {A B} (X : Event A) (Y : Event B) : Event (A * B) := *)
(*   fun ab => (X (fst ab) && Y (snd ab))%bool. *)

(* Axiom product_measure_on_rectangle : *)
(*   forall {A B} (μA : Meas A) (μB : Meas B) *)
(*          (X : Event A) (Y : Event B), *)
(*     Meas_fn (product_measure μA μB) (rectangle X Y) = Meas_fn μA X * Meas_fn μB Y. *)

(* Definition a_product_rel (M0 : Ensemble (Event Val)) : *)
(*   Ensemble (Event (option Val * option Val)) := *)
(*   fun (x : Event (option Val * option Val)) => *)
(*     M0 (fun v : Val => *)
(*           match v with *)
(*           | v_pair va ((v_clo _ _ _) as vf) => x (Some va, Some vf) *)
(*           | _ => false *)
(*           end). *)

(* Lemma apply_product_measure_integration : *)
(*   forall {X Y AT} (μa : Meas X) (μf : Meas Y) (A : AT) f, *)
(*    Integration *)
(*      (fun σ2 => *)
(*         Integration *)
(*           (fun va => Integration (fun vf => f vf va A σ2) μa) μf) *)
(*      μEntropy = *)
(*    Integration *)
(*      (fun σ2 => *)
(*         Integration *)
(*           (fun vavf => f (snd vavf) (fst vavf) A σ2) (product_measure μf μa)) *)
(*      μEntropy. *)
(* Proof. *)
(*   intros. *)
(*   apply f_equal2; auto. *)
(*   extensionality σ2. *)
(*   rewrite product_measure_integration. *)
(*   trivial. *)
(* Qed. *)

(* Lemma apply_lemma_3 : *)
(*   Integration *)
(*     (fun σ2 : Entropy => *)
(*        Integration (fun vavf => applyin (snd vavf) (fst vavf) A σ2) μ0) *)
(*     μEntropy = *)
(*   Integration *)
(*     (fun σ2 : Entropy => *)
(*        Integration (fun vavf => applyin (snd vavf) (fst vavf) A σ2) μ1) *)
(*     μEntropy. *)
(* Proof. *)
(*   intros. *)
(*   apply f_equal2; auto. *)
(*   extensionality σ2. *)
(*   rewrite (lemma_3 (a_product_rel (A_rel (τa ⨉ (τa ~> τr)))) μ0 μ1); auto. *)
(* Qed. *)

Definition at_most_one {A} (P : A -> Prop) :=
  forall x, P x -> (forall x', P x' -> x = x').

Lemma eval_a_at_most_one ρ e:
  at_most_one (fun v => EVAL_A ρ ⊢ e ⇓ v).
Proof.
  unfold at_most_one.
  intros v Hv v' Hv'.

  inversion Hv; subst; inversion Hv'; subst; auto. {
    rewrite H in H1.
    inversion H1; auto.
  }
Qed.

Lemma unfold_app_inside_evalin
      (ρ : Env Val)
      (ef ea : AExpr)
      (x : Var)
      (body : Expr)
      (ρ_clo : Env Val)
      (va : Val)
      (ev_f : EVAL_A ρ ⊢ ef ⇓ v_clo x body ρ_clo)
      (ev_a : EVAL_A ρ ⊢ ea ⇓ va)
      (A : Event Val)
  : evalin ρ (EC (ef @ ea)) A =
    evalin (ρ_clo[x → va]) body A.
Proof.
  extensionality σ.
  unfold evalin, ev, ew.

  decide_eval ρ as [app_v app_w app_ex app_u]. {
    decide_eval (ρ_clo[x → va]) as [vr wr exr ur]. {
      pose proof app_u (_, _) (EEC _ (EApp _ _ ev_f ev_a exr)).
      inversion H; subst.
      auto.
    } {
      contradict not_ex.
      exists (app_v, app_w).
      inversion app_ex.
      inversion H1.
      subst.

      rewrite (eval_a_at_most_one ρ ea _ ev_a _ H8).

      pose proof (eval_a_at_most_one ρ ef _ ev_f _ H6).
      inversion H; subst.
      auto.
    }
  } {
    decide_eval (ρ_clo[x → va]) as [vr0 wr0 exr0 ur0]; auto. {
      contradict not_ex.
      eexists (_, _).
      constructor.
      econstructor; eauto.
    }
  }
Qed.

Lemma compat_app Γ ef0 ef1 ea0 ea1 τa τr :
  (AEXP Γ ⊢ ef0 ≈ ef1 : (τa ~> τr)) ->
  (AEXP Γ ⊢ ea0 ≈ ea1 : τa) ->
  (EXP Γ ⊢ EC (ef0 @ ea0) ≈ EC (ef1 @ ea1) : τr).
Proof.
  intros Hf Ha.
  destruct Hf as [TCf0 [TCf1 Hf]].
  destruct Ha as [TCa0 [TCa1 Ha]].
  repeat econstructor; eauto.

  intros.
  pose proof (Hf _ _ X) as Hf.
  pose proof (Ha _ _ X) as Ha.
  intros A HA.

  destruct Hf as [[vf0 vf1] [f_vrel [ev_f0 ev_f1]]].
  destruct Ha as [[va0 va1] [a_vrel [ev_a0 ev_a1]]].
  unfold fst, snd in *.

  induction vf0, vf1; try (contradict f_vrel; fail).
  simpl in f_vrel.
  pose proof f_vrel va0 va1 a_vrel A HA.

  rename
    v into x0, e into body0, e0 into ρ_clo0,
  v0 into x1, e1 into body1, e2 into ρ_clo1.


  unfold μ.

  erewrite unfold_app_inside_evalin; eauto.
  erewrite unfold_app_inside_evalin; eauto.
Qed.

(*   intros Hf Ha. *)
(*   destruct Hf as [TCf0 [TCf1 Hf]]. *)
(*   destruct Ha as [TCa0 [TCa1 Ha]]. *)
(*   split3; try (apply TCApp with (τa0 := τa); assumption). *)

(*   intros. *)
(*   intros A HA. *)

(*   pose proof (Hf ρ0 ρ1 X) as agree_on_arrow. *)
(*   pose proof (Ha ρ0 ρ1 X) as agree_on_arg. *)
(*   clear Hf Ha (* TCf0 TCf1 TCa0 TCa1 *). *)

(*   unfold E_rel, E_rel' in *. *)

(*   unfold μ. *)

(*   rewrite 2 its_just_the_definition_of_applyin_how_hard_could_it_be. *)
(*   rewrite 2 its_just_applying_lemma_9_how_hard_could_it_be. *)
(*   rewrite 2 (its_just_applying_theorem_15_how_hard_could_it_be Γ τa τr); *)
(* try apply X; *)
(* auto. *)

(*   set (μa0 := meas_lift _). *)
(*   set (μf0 := meas_lift _). *)
(*   set (μa1 := meas_lift _). *)
(*   set (μf1 := meas_lift _). *)

(*   rewrite 2 apply_product_measure_integration. *)

(*   set (μ1 := product_measure _ _). *)
(*   set (μ2 := product_measure _ _). *)

(*   apply (apply_lemma_3 τa τr). { *)
(*   (* rewrite (lemma_3 (a_product_rel (A_rel (τa ⨉ (τa ~> τr))))). { *) *)
(*     intros. *)
(*     subst μ1 μ2. *)

(*     unfold a_product_rel in H. *)
(*     unfold A_rel, A_rel' in H. *)

(*     admit. *)
(*   } { *)
(*     intros. *)
(*     unfold preimage. *)
(*     unfold a_product_rel. *)
(*     intros v0 v1 vrel. *)
(*     destruct *)
(*       v0 as [| | va0 [| x0 body0 ρ_clo0 |]], *)
(*             v1 as [| | va1 [| x1 body1 ρ_clo1 |]]; *)
(* trivial; *)
(* inversion vrel; *)
(* try inversion H0. *)

(*     simpl. *)
(*     apply f_equal. *)
(*     clear B. *)

(*     pose proof H0 _ _ H _ HA as H0. *)
(*     simpl in H1. *)


(*   } *)

Lemma compat_plus Γ el0 er0 el1 er1 :
  (AEXP Γ ⊢ el0 ≈ el1 : ℝ) ->
  (AEXP Γ ⊢ er0 ≈ er1 : ℝ) ->
  (EXP Γ ⊢ EC (e_plus el0 er0) ≈ EC (e_plus el1 er1) : ℝ).
Proof.
  intros Hl Hr.
  destruct Hl as [TCl0 [TCl1 Hl]].
  destruct Hr as [TCr0 [TCr1 Hr]].
  split3; try (apply TCPlus; assumption).
  intros.
  pose proof (Hl _ _ X) as Hl.
  pose proof (Hr _ _ X) as Hr.
  intros A HA.

  congruence_μ.

  destruct Hl as [[vl0 vl1] [l_vrel [ev_l0 ev_l1]]].
  destruct Hr as [[vr0 vr1] [r_vrel [ev_r0 ev_r1]]].
  unfold fst, snd in *.

  induction vl0, vl1; try (contradict l_vrel; fail).
  induction vr0, vr1; try (contradict r_vrel; fail).
  simpl in l_vrel, r_vrel.
  subst.

  pose proof (EEC _ (EPlus _ σ ev_l0 ev_r0)) as E0.
  pose proof (EEC _ (EPlus _ σ ev_l1 ev_r1)) as E1.

  unfold evalin, ev, ew.
  decide_eval ρ0 as [v0 w0 ex0 u0].
  decide_eval ρ1 as [v1 w1 ex1 u1].

  injection (u0 (_, _) E0); intros.
  injection (u1 (_, _) E1); intros.
  subst.
  auto.
Qed.

Lemma compat_sample Γ :
  EXP Γ ⊢ EC e_sample ≈ EC e_sample : ℝ.
Proof.
  split3; try apply TCSample.
  intros.
  intros A HA.

  congruence_μ.

  pose proof EEC _ (ESample ρ0 σ) as E0.
  pose proof EEC _ (ESample ρ1 σ) as E1.

  unfold evalin, ev, ew.

  decide_eval ρ0 as [v0 w0 e0 u0].
  decide_eval ρ1 as [v1 w1 e1 u1].
  injection (u0 (_, _) E0); intros.
  injection (u1 (_, _) E1); intros.
  subst.
  auto.
Qed.

Lemma compat_factor Γ e0 e1:
  (AEXP Γ ⊢ e0 ≈ e1 : ℝ) ->
  (EXP Γ ⊢ EC (e_factor e0) ≈ EC (e_factor e1) : ℝ).
Proof.
  intro H.
  destruct H as [TC0 [TC1 H]].
  split3; try (apply TCFactor; assumption).
  intros.
  pose proof H ρ0 ρ1 X as H.

  intros A HA.

  congruence_μ.

  destruct H as [[v0 v1] [vrel [ev_0 ev_1]]].
  unfold fst, snd in *.

  induction v0, v1; try (contradict vrel; fail).
  simpl in vrel.
  subst.

  pose proof EEC _ (EFactor _ σ ev_0) as E0.
  pose proof EEC _ (EFactor _ σ ev_1) as E1.

  unfold evalin, ev, ew.
  decide_eval ρ0 as [v0 w0 ex0 u0].
  decide_eval ρ1 as [v1 w1 ex1 u1].
  injection (u0 (_, _) E0); intros.
  injection (u1 (_, _) E1); intros.
  subst.
  auto.
Qed.

Lemma unfold_for_let ρ x e er A
  : (fun σ => evalin ρ (e_let x e er) A σ) =
    (fun σ =>
       match ev ρ (EC e) (πL σ) with
       | Some v =>
         match ev (ρ[x → v]) er (πR σ) with
         | Some vr => if A vr then 1 else 0
         | None => 0
         end * ew (ρ[x → v]) er (πR σ)
       | None => 0
       end * ew ρ (EC e) (πL σ)).
Proof.
  extensionality σ.

  unfold evalin, ev, ew.

  decide_eval ρ as [v0 w0 ex0 u0];
  decide_eval ρ as [v1 w1 ex1 u1];
  try decide_eval (ρ[x → v1]) as [v2 w2 ex2 u2]. {
    inversion ex0; subst.
    inversion ex1; subst.

    pose proof ELet ρ σ H1 ex2 as E0.
    injection (u0 (_, _) E0).
    intros.
    subst.
    rewrite H.

    pose proof EEC _ H5 as E1.
    injection (u1 (_, _) E1); intros; subst.
    injection (u2 (_, _) H6); intros; subst.

    rewrite Rmult_assoc.
    apply f_equal2; auto.
    apply Rmult_comm.
  } {
    inversion ex0; subst.
    contradict not_ex.
    eexists (_, _).

    pose proof EEC _ H5 as E1.
    injection (u1 (_, _) E1); intros; subst.

    exact H6.
  } {
    inversion ex0; subst.
    contradict not_ex.
    eexists (_, _).

    pose proof EEC _ H5 as E0.
    exact E0.
  } {
    contradict not_ex.
    eexists (_, _).
    inversion ex1.
    econstructor; eauto.
  } {
    repeat rewrite Rmult_0_l.
    auto.
  } {
    auto.
  }
Qed.

(* Lemma apply_lemma_9 : _. *)

Lemma compat_let Γ x e0 er0 e1 er1 τ τr :
  (EXP Γ ⊢ EC e0 ≈ EC e1 : τ) ->
  (EXP (Γ[x → τ]) ⊢ er0 ≈ er1 : τr) ->
  (EXP Γ ⊢ e_let x e0 er0 ≈ e_let x e1 er1 : τr).
Proof.
  intros.

  destruct H as [tc_e0 [tc_e1 H]].
  destruct H0 as [TC_er0 [tc_er1 Hr]].

  repeat econstructor; intros; eauto.

  pose proof H _ _ X as e0_e1_rel.

  intros A HA.

  unfold μ.

  rewrite 2 unfold_for_let.

Qed.

Definition AExp_if_applicable e Γ τ :=
  match e with
  | EA e' => (AEXP Γ ⊢ e' ≈ e' : τ)
  | _ => True
  end.
Hint Unfold AExp_if_applicable.

Lemma fundamental_properties Γ e τ :
  (TC Γ ⊢ e : τ) ->
  (EXP Γ ⊢ e ≈ e : τ) /\ AExp_if_applicable e Γ τ.
Proof.
  intros.
  induction H; try (split; [|auto; fail]).
  - apply compat_let with (τ := τ0); tauto.
  - split; [apply compat_ea_real | apply compat_real].
  - split; [apply compat_ea_var | apply compat_var]; tauto.
  - split; [apply compat_ea_lam | apply compat_lam]; tauto.
  - apply compat_app with (τa := τa); tauto.
  - apply compat_plus; tauto.
  - apply compat_sample.
  - apply compat_factor; tauto.
Qed.

Print Assumptions fundamental_properties.
