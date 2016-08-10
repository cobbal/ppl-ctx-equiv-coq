(* Tested with coq 8.5pl1 *)

Require Import Basics.
Require Import Reals.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Local Open Scope R.

Record nnr := mknnr { _r : R; nnr_pos : 0 <= _r }.
Notation "R+" := nnr.

Program Definition nnr_mult (a b : R+) : R+ := mknnr (_r a * _r b) _.
Next Obligation.
  apply Rmult_le_pos.
  apply a.
  apply b.
Defined.
Hint Unfold nnr_mult.
Notation "a * b" := (nnr_mult a b).

Program Definition nnr_plus (a b : R+) : R+ := mknnr (_r a + _r b) _.
Next Obligation.
  replace 0 with (0 + 0) by apply Rplus_0_l.
  apply Rplus_le_compat; [apply a | apply b].
Qed.
Hint Unfold nnr_plus.
Notation "a + b" := (nnr_plus a b).

Program Definition nnr_0 := mknnr 0 (Rle_refl _).
Program Definition nnr_1 := mknnr 1 Rle_0_1.

Notation "a  '[>]'  b" := (Rgt_dec (_r a) (_r b)) (at level 70, no associativity).

Lemma nnr_eq_is_real_eq :
  forall (a b : R+), _r a = _r b -> a = b.
Proof.
  intros.
  destruct a as [a Ha], b as [b Hb].
  simpl in *.
  subst b.
  f_equal.
  apply proof_irrelevance.
Admitted.
Ltac nnr := apply nnr_eq_is_real_eq.

Theorem nnr_mult_comm (a b : R+) : a * b = b * a.
  nnr.
  unfold nnr_mult.
  apply Rmult_comm.
Qed.

Parameter Var : Type.
Parameter Var_eq_dec : forall x y : Var, {x = y} + {x <> y}.

Inductive Ty :=
| ℝ : Ty
| Arrow : Ty -> Ty -> Ty
.
Notation "x ~> y" := (Arrow x y) (at level 69, right associativity, y at level 70).

Inductive Expr :=
| e_let : Var -> CExpr -> Expr -> Expr
| EC : CExpr -> Expr
| EA : AExpr -> Expr
with AExpr :=
| e_real : R+ -> AExpr
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

| TCReal (r : R+)
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
| v_real : R+ -> Val
| v_clo : Var -> Expr -> Env Val -> Val
.

Definition Entropy := nat -> {r : R+ | 0 <= _r r /\ _r r <= 1}.

Definition Esplit : Entropy -> (Entropy * Entropy) :=
  fun σ =>
    ((fun n => σ (2 * n)%nat),
     (fun n => σ (2 * n + 1)%nat)).

Definition πL (σ : Entropy) : Entropy := fst (Esplit σ).
Definition πR (σ : Entropy) : Entropy := snd (Esplit σ).

Reserved Notation "'EVAL_E' ρ , σ ⊢ e ⇓ v , w" (at level 69, e at level 99, no associativity).
Reserved Notation "'EVAL_A' ρ ⊢ e ⇓ v" (at level 69, e at level 99, no associativity).
Reserved Notation "'EVAL_C' ρ , σ ⊢ e ⇓ v , w" (at level 69, e at level 99, no associativity).
Inductive eval (ρ : Env Val) : Entropy -> Expr -> Val -> R+ -> Prop :=
| ELet (σ : Entropy) {x : Var} {e0 : CExpr} {e1 : Expr} {v0 v1 : Val} {w0 w1 : R+}
  : (EVAL_C ρ, (πL σ) ⊢ e0 ⇓ v0, w0) ->
    (EVAL_E (ρ[x → v0]), (πR σ) ⊢ e1 ⇓ v1, w1) ->
    (EVAL_E ρ, σ ⊢ e_let x e0 e1 ⇓ v1, w0 * w1)
| EEA σ {e v}
  : (EVAL_A ρ ⊢ e ⇓ v) ->
    (EVAL_E ρ, σ ⊢ EA e ⇓ v, nnr_1)
| EEC {σ e v w}
  : (EVAL_C ρ, σ ⊢ e ⇓ v, w) ->
    (EVAL_E ρ, σ ⊢ EC e ⇓ v, w)
with eval_a (ρ : Env Val) : AExpr -> Val -> Prop :=
| EVar {x : Var} {v : Val}
  : ρ x = Some v ->
    (EVAL_A ρ ⊢ `x ⇓ v)
| EReal (r : R+)
  : (EVAL_A ρ ⊢ e_real r ⇓ v_real r)
| ELam (x : Var) (τ : Ty) (e : Expr)
  : (EVAL_A ρ ⊢ λ x ; τ , e ⇓ v_clo x e ρ)
with eval_c (ρ : Env Val) : Entropy -> CExpr -> Val -> R+ -> Prop :=
| EPlus (σ : Entropy) {e0 e1 : AExpr} {r0 r1 : R+}
  : (EVAL_A ρ ⊢ e0 ⇓ v_real r0) ->
    (EVAL_A ρ ⊢ e1 ⇓ v_real r1) ->
    (EVAL_C ρ, σ ⊢ e_plus e0 e1 ⇓ v_real (r0 + r1), nnr_1)
| EApp (σ : Entropy) {e0 e1 : AExpr}
       {x : Var} {body : Expr} {ρ_clo : Env Val}
       {v1 v2 : Val} {w : R+}
  : (EVAL_A ρ ⊢ e0 ⇓ v_clo x body ρ_clo) ->
    (EVAL_A ρ ⊢ e1 ⇓ v1) ->
    (EVAL_E (ρ_clo[x → v1]), σ ⊢ body ⇓ v2, w) ->
    (EVAL_C ρ, σ ⊢ e0 @ e1 ⇓ v2, w)
| ESample (σ : Entropy)
  : (EVAL_C ρ, σ ⊢ e_sample ⇓ v_real (proj1_sig (σ 0%nat)), nnr_1)
| EFactor (σ : Entropy) {e : AExpr} {r : R+}
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
   format "'[' 'existsT'  '/ ' x .. y , '/ ' p ']'")
  : type_scope.

Definition uniqueT {A : Type} (P : A -> Type) (x : A) :=
  (P x * forall x' : A, P x' -> x = x')%type.

Notation "'existsT' ! x .. y , p" :=
  (sigT (uniqueT (fun x => .. (sigT (uniqueT (fun y => p))) ..)))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' !  '/ ' x .. y , '/ ' p ']'")
    : type_scope.

Axiom eval_dec :
  forall ρ e σ,
    (existsT! vw : (Val * R+), let (v, w) := vw in EVAL_E ρ, σ ⊢ e ⇓ v, w) +
    ((existsT vw : (Val * R+), let (v, w) := vw in EVAL_E ρ, σ ⊢ e ⇓ v, w) -> False).

Definition option0 : option R+ -> R+ :=
  fun o =>
    match o with
    | Some r => r
    | None => nnr_0
    end.

Definition compose {A B C} (f : B -> C) (g : A -> B) : A -> C :=
  fun a => f (g a).
Notation "f ∘ g" := (compose f g).


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

Definition ew ρ e σ : R+ :=
  match eval_dec ρ e σ with
  | inl (existT _ (v, w) _) => w
  | inr _ => nnr_0
  end.
Definition Indicator (b : bool) : R+ := if b then nnr_1 else nnr_0.

Definition evalin ρ e (V : Event Val) σ : R+ :=
  match ev ρ e σ with
  | Some v => Indicator (V v)
  | None => nnr_0
  end * ew ρ e σ.

Definition applyin (v v' : option Val) A σ :=
  match v, v' with
  | Some (v_clo x e ρ), Some v' => evalin (ρ[x → v']) e A σ
  | _, _ => nnr_0
  end.
Definition Meas A := Event A -> R+.
Axiom μEntropy : Meas Entropy.

Axiom Integration : forall {A}, (A -> R+) -> Meas A -> R+.
(* Notation "'∫' fx ';' μ ( 'd' x )" := (Integration (fun x => fx) μ). *)

Axiom Integration_linear :
  forall {A} (μ : Meas A) (c : R+) (f : A -> R+),
    c * Integration f μ = Integration (fun x => c * f x) μ.

Definition bool_of_dec {A B} : sumbool A B -> bool :=
  fun x => if x then true else false.

Axiom lebesgue_pos_measure : Meas R+.
Axiom lebesgue_pos_measure_interval :
  forall (r : R+),
    lebesgue_pos_measure (fun x => bool_of_dec (r [>] x)) = r.

Axiom riemann_def_of_lebesgue_integration :
  forall {A} μ (f : A -> R+),
    Integration f μ =
    Integration
      (fun t => μ (fun x => bool_of_dec (f x [>] t)))
      lebesgue_pos_measure.

Axiom int_const_entropy :
  forall (v : R+)
         (f : Entropy -> R+),
    (forall x, f x = v) ->
    Integration f μEntropy = v.

Axiom integration_of_indicator :
  forall {A}
         (m : Meas A)
         (f : A -> bool),
    Integration (fun x => Indicator (f x)) m = m f.


(* Axiom μ : forall τ : Ty, Env Val -> Expr -> Event -> R. *)
Definition μ ρ e V :=
  Integration (fun σ => evalin ρ e V σ) μEntropy.

Definition A_rel (V_rel : Ty -> Val -> Val -> Type) (τ : Ty) (A0 A1 : Event Val) :=
  forall v0 v1,
    V_rel τ v0 v1 ->
    (A0 v0 = A1 v1).

Definition E_rel (V_rel : Ty -> Val -> Val -> Prop) (τ : Ty) (c0 c1 : Config) : Prop :=
  let (ρ0, e0) := c0 in
  let (ρ1, e1) := c1 in
  forall A0 A1, A_rel V_rel τ A0 A1 ->
            μ ρ0 e0 A0 = μ ρ1 e1 A1.

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
  end
where "'VREL' v0 , v1 ∈ V[ τ ]" := (V_rel τ v0 v1)
.
Notation "'EREL' e0 , e1 ∈ E[ τ ]" :=
  (E_rel V_rel τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, τ at level 99).
Notation "'EAREL' e0 , e1 ∈ E[ τ ]" :=
  (EA_rel V_rel τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, τ at level 99).
Notation "'AREL' A0 , A1 ∈ A[ τ ]" :=
  (A_rel V_rel τ A0 A1)
    (at level 69, A0 at level 99, A1 at level 99, τ at level 99).

Definition env_dom_eq {A B} (envA : Env A) (envB : Env B) :=
  forall x, envA x = None <-> envB x = None.
Record env_models {ρ : Env Val} {Γ : Env Ty} : Type :=
  {
    env_dom_match : env_dom_eq Γ ρ;
    env_val_models : forall x τ,
        Γ x = Some τ ->
        {v | ρ x = Some v}
  }.
Notation "'ENV' ρ ⊨ Γ" := (@env_models ρ Γ) (at level 69, no associativity).

Record G_rel {Γ : Env Ty} {ρ0 ρ1 : Env Val}: Type :=
  {
    G_rel_modeling0 : ENV ρ0 ⊨ Γ;
    G_rel_modeling1 : ENV ρ1 ⊨ Γ;
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
  forall {ρ0 ρ1},
    (GREL ρ0, ρ1 ∈ G[Γ]) ->
    (EREL (ρ0, e0), (ρ1, e1) ∈ E[τ]).
Notation "'EXP' Γ ⊢ e0 ≈ e1 : τ" :=
  (related_exprs Γ τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, no associativity).
Definition related_aexprs (Γ : Env Ty) (τ : Ty) (e0 e1 : AExpr) :=
  (TC_A Γ ⊢ e0 : τ) /\
  (TC_A Γ ⊢ e1 : τ) /\
  forall {ρ0 ρ1},
    (GREL ρ0, ρ1 ∈ G[Γ]) ->
    (EAREL (ρ0, e0), (ρ1, e1) ∈ E[τ]).
Notation "'AEXP' Γ ⊢ e0 ≈ e1 : τ" :=
  (related_aexprs Γ τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, no associativity).

(* absurdly common typo I'm sick of correcting *)
Ltac inductino a := induction a.

Ltac decide_eval' ρ v w e u :=
  let not_ex := fresh "not_ex" in
  destruct (eval_dec ρ) as [[[v w] [e u]] | not_ex];
  [| try (contradict not_ex; eexists (_, _); repeat constructor; eassumption)].
Tactic Notation "decide_eval" constr(ρ) "as"
       "[" ident(v) ident(w) ident(e) ident(u) "]"
  := (decide_eval' ρ v w e u).

Ltac congruence_μ := unfold μ; f_equal; extensionality σ.

Lemma compat_real Γ r :
  AEXP Γ ⊢ e_real r ≈ e_real r : ℝ.
Proof.
  repeat constructor.
  intros ρ0 ρ1 Hρ.
  exists (v_real r, v_real r); simpl.
  repeat constructor.
Qed.

Lemma compat_ea_real Γ r :
  EXP Γ ⊢ EA (e_real r) ≈ EA (e_real r) : ℝ.
Proof.
  repeat constructor.
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  congruence_μ.

  unfold evalin, ew, ev.
  decide_eval ρ0 as [v0 w0 ex0 u0]; simpl in *.
  decide_eval ρ1 as [v1 w1 ex1 u1]; simpl in *.

  inversion ex0.
  inversion ex1.
  inversion H1.
  inversion H6.
  subst.

  nnr.
  do 3 f_equal.

  apply HA.
  simpl.
  auto.
Qed.

Lemma compat_var Γ x τ :
  Γ x = Some τ ->
  AEXP Γ ⊢ `x ≈ `x : τ.
Proof.
  intros.
  repeat constructor; auto.

  intros ρ0 ρ1 Hρ.

  induction (env_val_models (G_rel_modeling0 Hρ) x τ H) as [v0 Hv0].
  induction (env_val_models (G_rel_modeling1 Hρ) x τ H) as [v1 Hv1].
  pose proof (G_rel_V Hρ H Hv0 Hv1) as Hv.

  exists (v0, v1); simpl.
  repeat constructor; auto.
Qed.

Lemma compat_ea_var Γ x τ :
  Γ x = Some τ ->
  EXP Γ ⊢ EA (`x) ≈ EA (`x) : τ.
Proof.
  intros.
  repeat constructor; auto.
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  induction (env_val_models (G_rel_modeling0 Hρ) x τ H) as [v0 Hv0].
  induction (env_val_models (G_rel_modeling1 Hρ) x τ H) as [v1 Hv1].
  pose proof (G_rel_V Hρ H Hv0 Hv1) as Hv.

  congruence_μ.

  unfold evalin, ev, ew.
  pose proof EEA _ σ (EVar _ Hv0) as EVAL_0.
  pose proof EEA _ σ (EVar _ Hv1) as EVAL_1.

  decide_eval ρ0 as [ve0 w0 ex0 u0].
  decide_eval ρ1 as [ve1 w1 ex1 u1].

  injection (u0 (_, _) EVAL_0); intros.
  injection (u1 (_, _) EVAL_1); intros.
  subst.
  do 2 f_equal.
  auto.
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
  intros Hbody.
  repeat constructor; try apply Hbody.
  intros ρ0 ρ1 Hρ.

  exists (v_clo x body0 ρ0, v_clo x body1 ρ1); simpl.
  repeat constructor.

  intros va0 va1 Hva.
  intros A0 A1 HA.

  apply Hbody; auto.
  apply extend_grel; auto.
Qed.

Lemma compat_ea_lam Γ x body0 body1 τa τr :
  (EXP Γ[x → τa] ⊢ body0 ≈ body1 : τr) ->
  (EXP Γ ⊢ EA (λ x ; τa, body0) ≈ EA (λ x ; τa, body1) : (τa ~> τr)).
Proof.
  intro Hbody.
  repeat constructor; try apply Hbody.
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  congruence_μ.

  pose proof EEA _ σ (ELam ρ0 x τa body0) as EVAL_0.
  pose proof EEA _ σ (ELam ρ1 x τa body1) as EVAL_1.

  unfold evalin, ev, ew.
  decide_eval ρ0 as [v0 w0 ex0 u0].
  decide_eval ρ1 as [v1 w1 ex1 u1].

  injection (u0 (_, _) EVAL_0); intros tH0a tH0b.
  injection (u1 (_, _) EVAL_1); intros tH1a tH1b.
  subst.

  do 2 f_equal.

  apply HA.
  intros va0 va1 Hva.

  apply Hbody; auto.
  apply extend_grel; auto.
Qed.

(* Ltac riemann_it := *)
(*   rewrite riemann_def_of_lebesgue_integration; *)
(*   apply eq_sym; *)
(*   rewrite riemann_def_of_lebesgue_integration; *)
(*   apply eq_sym; *)
(*   f_equal; *)
(*   extensionality t. *)

(* Ltac riemann_biimplicate := *)
(*          induction Rgt_dec as [gt0 | ngt0], Rgt_dec as [gt1 | ngt1]; auto; *)
(*          [ contradict ngt1 | contradict ngt0 ]. *)

Axiom prod_meas : forall {A B}, Meas A -> Meas B -> Meas (A * B).

Lemma tonelli_1 :
  forall {A B} (f : A -> B -> R+) (μx : Meas A) (μy : Meas B),
    Integration (fun x => Integration (fun y => f x y) μy) μx =
    Integration (fun xy => f (fst xy) (snd xy)) (prod_meas μx μy).
Admitted.

Lemma tonelli_2 :
  forall {A B} (f : A -> B -> R+) (μx : Meas A) (μy : Meas B),
    Integration (fun xy => f (fst xy) (snd xy)) (prod_meas μx μy) =
    Integration (fun y => Integration (fun x => f x y) μx) μy.
Admitted.

Lemma tonelli_3 :
  forall {A B} (f : A -> B -> R+) (μx : Meas A) (μy : Meas B),
    Integration (fun x => Integration (fun y => f x y) μy) μx =
    Integration (fun y => Integration (fun x => f x y) μx) μy.
Admitted.

Lemma lemma_1 :
  forall {A B} (f : A -> B -> R+) (μx : Meas A) (μy : Meas B),
    Integration (fun x => Integration (fun y => f x y) μy) μx =
    Integration (fun y => Integration (fun x => f x y) μx) μy.
Proof @tonelli_3.

Lemma lemma_9 : forall (g : Entropy -> Entropy -> R+),
    Integration (fun σ => g (πL σ) (πR σ)) μEntropy =
    Integration (fun σR => Integration (fun σL => g σL σR) μEntropy) μEntropy.
Proof.
  intros.
Admitted.

Lemma if_bool_if_simplify :
  forall {A B C} (x : {A} + {B}) (a b : C),
  (if bool_of_dec x then a else b) = (if x then a else b).
Proof.
  intros.
  induction x; auto.
Qed.

Theorem theorem_15 :
  forall (f : Val -> R+) {Γ e τ ρ},
    (TC Γ ⊢ e : τ) ->
    (ENV ρ ⊨ Γ) ->
    Integration f (μ ρ e) =
    Integration (fun σ => option0 (f <$> (ev ρ e σ)) * ew ρ e σ) μEntropy.
Proof.
  intros.

  unfold μ.

  rewrite riemann_def_of_lebesgue_integration.
  rewrite lemma_1.
  unfold evalin.

  match goal with
  | [ |- _ (fun y => _ (fun x => ?v * ?w) _) _ = _ ] =>
    assert ((fun y : Entropy => Integration (fun x => v * w) lebesgue_pos_measure) =
            (fun y : Entropy => Integration (fun x => v) lebesgue_pos_measure * w))
  end.
  {
    extensionality σ.
    rewrite nnr_mult_comm.
    rewrite Integration_linear.
    f_equal.
    extensionality x.
    apply nnr_mult_comm.
  }
  rewrite H0.
  clear H0.

  f_equal.
  extensionality σ.

  generalize (ew ρ e σ) as w, (ev ρ e σ) as v.
  intros.

  f_equal.
  unfold option0, option_map.
  induction v; auto. {
    rewrite integration_of_indicator.
    apply lebesgue_pos_measure_interval.
  } {
    replace (fun _ => nnr_0) with (fun _ : R+ => nnr_0 * nnr_0)
      by (extensionality z; nnr; apply Rmult_0_l).
    rewrite <- Integration_linear.
    nnr.
    apply Rmult_0_l.
  }
Qed.

Definition preimage {A B R} (f : A -> B) : (B -> R) -> (A -> R) :=
  fun eb a => eb (f a).

Definition ensemble_of_event {X} : Event X -> Ensemble X :=
  fun A x => A x = true.

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

  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  pose proof (Hf _ _ Hρ) as Hf.
  pose proof (Ha _ _ Hρ) as Ha.

  destruct Hf as [[vf0 vf1] [f_vrel [ev_f0 ev_f1]]].
  destruct Ha as [[va0 va1] [a_vrel [ev_a0 ev_a1]]].
  unfold fst, snd in *.

  induction vf0, vf1; try tauto.

  rename
    v into x0, e into body0, e0 into ρ_clo0,
  v0 into x1, e1 into body1, e2 into ρ_clo1.

  pose proof f_vrel va0 va1 a_vrel A0 A1 HA as f_vrel.

  unfold μ.

  do 2 (erewrite unfold_app_inside_evalin; eauto).
Qed.

Lemma compat_plus Γ el0 er0 el1 er1 :
  (AEXP Γ ⊢ el0 ≈ el1 : ℝ) ->
  (AEXP Γ ⊢ er0 ≈ er1 : ℝ) ->
  (EXP Γ ⊢ EC (e_plus el0 er0) ≈ EC (e_plus el1 er1) : ℝ).
Proof.
  intros Hl Hr.
  destruct Hl as [tc_l0 [tc_l1 Hl]].
  destruct Hr as [tc_r0 [tc_r1 Hr]].
  repeat constructor; auto.
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  pose proof (Hl _ _ Hρ) as Hl.
  pose proof (Hr _ _ Hρ) as Hr.

  congruence_μ.

  destruct Hl as [[vl0 vl1] [l_vrel [ev_l0 ev_l1]]].
  destruct Hr as [[vr0 vr1] [r_vrel [ev_r0 ev_r1]]].
  unfold fst, snd in *.

  induction vl0, vl1; try tauto.
  induction vr0, vr1; try tauto.
  simpl in l_vrel, r_vrel.
  subst.

  pose proof (EEC _ (EPlus _ σ ev_l0 ev_r0)) as EVAL_0.
  pose proof (EEC _ (EPlus _ σ ev_l1 ev_r1)) as EVAL_1.

  unfold evalin, ev, ew.
  decide_eval ρ0 as [v0 w0 ex0 u0].
  decide_eval ρ1 as [v1 w1 ex1 u1].

  injection (u0 (_, _) EVAL_0); intros.
  injection (u1 (_, _) EVAL_1); intros.
  subst.

  do 2 f_equal.
  apply HA.
  simpl.
  reflexivity.
Qed.

Lemma compat_sample Γ :
  EXP Γ ⊢ EC e_sample ≈ EC e_sample : ℝ.
Proof.
  repeat constructor.
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  congruence_μ.

  pose proof EEC _ (ESample ρ0 σ) as EVAL_0.
  pose proof EEC _ (ESample ρ1 σ) as EVAL_1.

  unfold evalin, ev, ew.

  decide_eval ρ0 as [v0 w0 e0 u0].
  decide_eval ρ1 as [v1 w1 e1 u1].
  injection (u0 (_, _) EVAL_0); intros.
  injection (u1 (_, _) EVAL_1); intros.
  subst.

  do 2 f_equal.
  apply HA.
  simpl.
  reflexivity.
Qed.

Lemma compat_factor Γ e0 e1:
  (AEXP Γ ⊢ e0 ≈ e1 : ℝ) ->
  (EXP Γ ⊢ EC (e_factor e0) ≈ EC (e_factor e1) : ℝ).
Proof.
  intro H.
  destruct H as [TC0 [TC1 H]].
  repeat constructor; auto.
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  pose proof H ρ0 ρ1 Hρ as H.

  congruence_μ.

  destruct H as [[v0 v1] [vrel [ev_0 ev_1]]].
  unfold fst, snd in *.

  induction v0, v1; try tauto.
  simpl in vrel.
  subst.

  pose proof EEC _ (EFactor _ σ ev_0) as EVAL_0.
  pose proof EEC _ (EFactor _ σ ev_1) as EVAL_1.

  unfold evalin, ev, ew.
  decide_eval ρ0 as [v0 w0 ex0 u0].
  decide_eval ρ1 as [v1 w1 ex1 u1].
  injection (u0 (_, _) EVAL_0); intros.
  injection (u1 (_, _) EVAL_1); intros.
  subst.

  do 2 f_equal.
  apply HA.
  simpl.
  reflexivity.
Qed.

Definition resist_folding {A} (x : A) := x.

Lemma unfold_for_let ρ x e er A
  : (fun σ => evalin ρ (e_let x e er) A σ) =
    (fun σ =>
       resist_folding (fun σL σR =>
          (option0
             ((fun v =>
                 option0 ((Indicator ∘ A) <$> ev (ρ[x → v]) er σR) *
                 ew (ρ[x → v]) er σR
              ) <$> ev ρ (EC e) σL))
          * ew ρ (EC e) σL) (πL σ) (πR σ)).
Proof.
  unfold resist_folding.
  extensionality σ.

  unfold evalin, ev, ew.

  decide_eval ρ as [v0 w0 ex0 u0];
decide_eval ρ as [v1 w1 ex1 u1];
simpl;
try decide_eval (ρ[x → v1]) as [v2 w2 ex2 u2]; try (nnr; simpl; ring). {
    inversion ex0; subst.
    inversion ex1; subst.

    pose proof ELet ρ σ H1 ex2 as EVAL_0.
    injection (u0 (_, _) EVAL_0).
    intros.
    nnr.
    simpl.
    subst.
    rewrite H.

    pose proof EEC _ H5 as EVAL_1.
    injection (u1 (_, _) EVAL_1); intros; subst.
    injection (u2 (_, _) H6); intros; subst.

    rewrite Rmult_assoc.
    f_equal.
    apply Rmult_comm.
  } {
    inversion ex0; subst.
    contradict not_ex.
    eexists (_, _).

    pose proof EEC _ H5 as EVAL_1.
    injection (u1 (_, _) EVAL_1); intros; subst.

    exact H6.
  } {
    inversion ex0; subst.
    contradict not_ex.
    eexists (_, _).

    pose proof EEC _ H5 as EVAL_0.
    exact EVAL_0.
  } {
    contradict not_ex.
    eexists (_, _).
    inversion ex1.
    econstructor; eauto.
  }
Qed.


Lemma by_theorem_15 ρ x e er A Γ τ :
  (TC_C Γ ⊢ e : τ) ->
  (ENV ρ ⊨ Γ) ->
    Integration (fun σ => evalin ρ (e_let x e er) A σ) μEntropy =
    Integration (fun σ1 =>
    Integration (fun v =>
                   evalin (ρ[x → v]) er A σ1
                ) (μ ρ (EC e))
                ) μEntropy.
Proof.
  intros.
  rewrite unfold_for_let.

  rewrite lemma_9.
  unfold resist_folding.

  f_equal.
  extensionality σ1.

  erewrite theorem_15; eauto.

  f_equal.
  extensionality σ0.

  do 2 f_equal.
  unfold option_map, evalin.
  induction ev, ev; auto.
Qed.

Lemma meas_compat_integration :
  forall (τ : Ty)
         (A0' A1' : Event Val)
         (μ0 μ1 : Meas Val)
         (μ0' μ1' : Val -> Meas Val),
    (forall A0 A1, AREL A0, A1 ∈ A[τ] -> μ0 A0 = μ1 A1) ->
    (forall (v0 v1 : Val),
        (VREL v0, v1 ∈ V[τ]) ->
        μ0' v0 A0' = μ1' v1 A1') ->
    Integration (fun v => μ0' v A0') μ0 =
    Integration (fun v => μ1' v A1') μ1.
Proof.
  intros.

  rewrite (riemann_def_of_lebesgue_integration μ0).
  rewrite (riemann_def_of_lebesgue_integration μ1).
  f_equal.
  extensionality t.

  apply H.
  intros v0 v1 Hv.

  rewrite (H0 _ _ Hv).
  reflexivity.
Qed.

Lemma compat_let Γ x e0 er0 e1 er1 τ τr :
  (EXP Γ ⊢ EC e0 ≈ EC e1 : τ) ->
  (EXP (Γ[x → τ]) ⊢ er0 ≈ er1 : τr) ->
  (EXP Γ ⊢ e_let x e0 er0 ≈ e_let x e1 er1 : τr).
Proof.
  intros He Her.
  destruct He as [tc_e0 [tc_e1 He]].
  destruct Her as [tc_er0 [tc_er1 Her]].
  repeat econstructor; eauto.

  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  unfold μ.

  erewrite 2 by_theorem_15; eauto; try apply Hρ.

  rewrite 2 lemma_1 with (μx := μEntropy).

  eapply meas_compat_integration with
    (μ0' := fun v => μ (ρ0[x → v]) er0)
    (μ1' := fun v => μ (ρ1[x → v]) er1).
  {
    apply He.
    apply Hρ.
  } {
    intros v0 v1 Hv.
    apply Her; auto.
    apply extend_grel; auto.
  }
Qed.


Definition AExp_related_if_applicable e Γ τ :=
  match e with
  | EA e' => (AEXP Γ ⊢ e' ≈ e' : τ)
  | _ => True
  end.
Hint Unfold AExp_related_if_applicable.

Lemma fundamental_properties Γ e τ :
  (TC Γ ⊢ e : τ) ->
  (EXP Γ ⊢ e ≈ e : τ) /\ AExp_related_if_applicable e Γ τ.
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
