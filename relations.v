(* Tested with coq 8.5pl1 *)

Require Import Basics.
Require Import Reals.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics.
Require Import nnr.

Local Open Scope R.

Notation "a  '⨉'  b" := (prod a b) (at level 40, left associativity).

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
Notation "ρ [ x → v ]" := (extend ρ x v) (at level 68, left associativity).

Definition env_dom_eq {A B} (envA : Env A) (envB : Env B) :=
  forall x, envA x = None <-> envB x = None.

Reserved Notation "'TC' Γ ⊢ e : τ" (at level 70, e at level 99, no associativity).
Inductive tc {Γ : Env Ty} : Expr -> Ty -> Prop :=
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

Definition Entropy := nat -> {r : R | 0 <= r <= 1}.

Definition πL (σ : Entropy) : Entropy := fun n => σ (2 * n)%nat.
Definition πR (σ : Entropy) : Entropy := fun n => σ (2 * n + 1)%nat.

Fixpoint π (n : nat) (σ : Entropy) : Entropy :=
  match n with
  | O => πL σ
  | S n' => π n' (πR σ)
  end.

Record env_models {ρ : Env Val} {Γ : Env Ty} : Type :=
  {
    env_dom_match : env_dom_eq Γ ρ;
    env_val_models : forall x τ,
        Γ x = Some τ ->
        {v | ρ x = Some v}
  }.
Notation "'ENV' ρ ⊨ Γ" := (@env_models ρ Γ) (at level 69, no associativity).

Lemma env_model_extend
           {ρ Γ} (Hρ : ENV ρ ⊨ Γ) (x : Var) (v : Val) (τ : Ty)
  : ENV ρ[x → v] ⊨ Γ[x → τ].
Proof.
  unfold extend.
  repeat constructor. {
    destruct Var_eq_dec; intros H. {
      inversion H.
    } {
      apply Hρ.
      auto.
    }
  } {
    destruct Var_eq_dec; intros H. {
      inversion H.
    } {
      apply Hρ.
      auto.
    }
  } {
    intros.
    destruct Var_eq_dec. {
      exists v; auto.
    } {
      eapply env_val_models; eauto.
    }
  }
Qed.

Definition eval_a ρ (e : AExpr) : option Val :=
  match e with
  | e_real r => Some (v_real r)
  | e_lam x body => Some (v_clo x body ρ)
  | e_var x => ρ x
  end.

Reserved Notation "'EVAL' ρ , σ ⊢ e ⇓ v , w" (at level 69, e at level 99, no associativity).
Inductive eval (ρ : Env Val) (σ : Entropy) : forall (e : Expr) (v : Val) (w : R+), Prop :=
| EPure (ae : AExpr) (v : Val) :
    eval_a ρ ae = Some v ->
    (EVAL ρ, σ ⊢ e_pure ae ⇓ v, nnr_1)
| EApp {e0 e1 : Expr}
       {x : Var} {body : Expr} {ρ_clo : Env Val}
       {v1 v2 : Val}
       {w0 w1 w2 : R+}
  : (EVAL ρ, (π 0 σ) ⊢ e0 ⇓ v_clo x body ρ_clo, w0) ->
    (EVAL ρ, (π 1 σ) ⊢ e1 ⇓ v1, w1) ->
    (EVAL ρ_clo[x → v1], (π 2 σ) ⊢ body ⇓ v2, w2) ->
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

Definition Config := Env Val ⨉ Expr.

Definition Event X := X -> bool.

Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsT'  '/ ' x .. y , '/ ' p ']'")
  : type_scope.

Definition uniqueT {A : Type} (P : A -> Type) (x : A) :=
  P x ⨉ forall x' : A, P x' -> x = x'.

Notation "'existsT' ! x .. y , p" :=
  (sigT (uniqueT (fun x => .. (sigT (uniqueT (fun y => p))) ..)))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' !  '/ ' x .. y , '/ ' p ']'")
    : type_scope.

Axiom eval_dec :
  forall ρ e σ,
    (existsT! vw : (Val * R+), let (v, w) := vw in EVAL ρ, σ ⊢ e ⇓ v, w) +
    ((existsT vw : (Val * R+), let (v, w) := vw in EVAL ρ, σ ⊢ e ⇓ v, w) -> False).

Definition TCEnv' (TCVal : Val -> Ty -> Type) (ρ : Env Val) (Γ : Env Ty) : Type :=
  (env_dom_eq Γ ρ) *
  forall x τ,
    Γ x = Some τ ->
    {v : Val & (ρ x = Some v) ⨉ TCVal v τ}
.

Inductive TCVal : Val -> Ty -> Type :=
| TCVReal (r : R) : TCVal (v_real r) ℝ
| TCVClo x body ρ Γ τa τr :
    (TC (Γ[x → τa]) ⊢ body : τr) ->
    TCEnv' TCVal ρ Γ ->
    TCVal (v_clo x body ρ) (τa ~> τr)
.

Definition TCEnv := TCEnv' TCVal.

Lemma TCEnv_extend Γ ρ x v τ :
  TCEnv ρ Γ ->
  TCVal v τ ->
  TCEnv (ρ[x → v]) (Γ[x → τ]).
Proof.
  intros.
  unfold extend.
  destruct X.
  split. {
    intro y.
    destruct Var_eq_dec; auto.
    split; intros; inversion H.
  } {
    intros.
    destruct Var_eq_dec. {
      exists v.
      split; auto.
      injection H.
      intros.
      subst.
      auto.
    } {
      apply s.
      auto.
    }
  }
Qed.

Lemma eval_dec' Γ e τ ρ σ :
    (TC Γ ⊢ e : τ) ->
    (TCEnv ρ Γ) ->
    (existsT! vw : (Val * R+), let (v, w) := vw in
                               (TCVal v τ)
                                 ⨉ (EVAL ρ, σ ⊢ e ⇓ v, w)) +
    ((existsT vw : (Val * R+), let (v, w) := vw in EVAL ρ, σ ⊢ e ⇓ v, w) -> False).
Proof.
  intros H Hρ.
  revert ρ Hρ.

  (* induction H. { *)
  (*   intros. *)
  (*   case (IHtc1 ρ); intros; auto. { *)
  (*     destruct s as [[v0 w0] [ex0 u0]]. *)
  (*     case (IHtc2 (ρ[x → v0])); intros. { *)
  (*       apply TCEnv_extend; auto. *)
  (*       apply ex0. *)
  (*     } { *)
  (*       admit. *)
  (*     } *)
  (*     admit. *)

  (*   } *)
Admitted.

Definition fromOption {A} (d : A) (opt : option A) : A :=
  match opt with
  | Some a' => a'
  | None => d
  end.

Definition option0 : option R+ -> R+ := fromOption nnr_0.

Notation "f ∘ g" := (compose f g).

Notation "f <$> x" := (option_map f x) (at level 20, left associativity).
Definition option_ap {A B} (o_f : option (A -> B)) : option A -> option B :=
  fun a =>
    match o_f with
    | Some f => f <$> a
    | None => None
    end.
Notation "f <*> x" := (option_ap f x) (at level 20).

Definition option_rbind {A B} (f : A -> option B) : option A -> option B :=
  fun o_a =>
    match o_a with
    | Some a => f a
    | None => None
    end.
Notation "f =<< x" := (option_rbind f x) (at level 20).

Definition id {A} := @Datatypes.id A.

Definition option_join {A} : option (option A) -> option A :=
  fun x => id =<< x.

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

Definition resist_folding {A} (x : A) := x.

Definition ifte {X} (a : bool) (b c : X) := if a then b else c.
Definition Indicator {X} (b : Event X) : X -> R+ := fun x => ifte (b x) nnr_1 nnr_0.

Definition eval_in ρ e (A : Event Val) σ : R+ :=
  option0 (Indicator A <$> ev ρ e σ) [*] ew ρ e σ.

Definition Meas A := (Event A -> R+).
Axiom μEntropy : Meas Entropy.

Axiom Integration : forall {A}, (A -> R+) -> Meas A -> R+.
(* Notation "'∫' fx ';' μ ( 'd' x )" := (Integration (fun x => fx) μ). *)

Axiom Integration_linear :
  forall {A} (μ : Meas A) (s0 s1 : R+) (f0 f1 : A -> R+),
    s0 [*] Integration f0 μ [+] s1 [*] Integration f1 μ =
    Integration (fun x => s0 [*] f0 x [+] s1 [*] f1 x) μ.

Lemma Integration_linear_mult_r :
  forall {A} (μ : Meas A) (s : R+) (f : A -> R+),
    Integration f μ [*] s =
    Integration (fun x => f x [*] s) μ.
Proof.
  intros.
  nnr.
  simpl.
  rewrite Rmult_comm.
  rewrite <- Rplus_0_r at 1.
  rewrite <- Rmult_0_l with (r := _r (Integration (const nnr_0) μ)).
  replace 0 with (_r nnr_0) by auto.

  replace (_ + _) with
  (_r (s [*] Integration f μ [+] nnr_0 [*] Integration (const nnr_0) μ))
    by auto.
  f_equal.
  rewrite Integration_linear.
  f_equal.
  extensionality x.
  nnr.
  simpl.
  ring.
Qed.

Lemma Integration_linear_mult_l :
  forall {A} (μ : Meas A) (s : R+) (f : A -> R+),
    s [*] Integration f μ =
    Integration (fun x => s [*] f x) μ.
Proof.
  intros.
  rewrite nnr_mult_comm.
  replace (fun x => s [*] f x) with (fun x => f x [*] s). {
    apply Integration_linear_mult_r.
  }
  extensionality x.
  apply nnr_mult_comm.
Qed.

Definition bool_of_dec {A B} : sumbool A B -> bool :=
  fun x => if x then true else false.

Axiom lebesgue_measure : Meas R.
Axiom lebesgue_measure_interval :
  forall (r : R+),
    lebesgue_measure (fun x => bool_of_dec (r [>] x)) = r.

Axiom riemann_def_of_lebesgue_integration :
  forall {A} μ (f : A -> R+),
    Integration f μ =
    Integration
      (fun t => μ (fun x => bool_of_dec (f x [>] t)))
      lebesgue_measure.

Axiom integration_of_indicator :
  forall {A}
         (m : Meas A)
         (f : Event A),
    Integration (fun x => Indicator f x) m = m f.

Definition μ ρ e V :=
  Integration (fun σ => eval_in ρ e V σ) μEntropy.

Definition A_rel' (V_rel : Ty -> Val -> Val -> Type) (τ : Ty) (A0 A1 : Event Val) :=
  forall v0 v1,
    V_rel τ v0 v1 ->
    (A0 v0 = (* iff *) A1 v1).

Definition E_rel (V_rel : Ty -> Val -> Val -> Prop) (τ : Ty) (c0 c1 : Config) : Prop :=
  let (ρ0, e0) := c0 in
  let (ρ1, e1) := c1 in
  forall A0 A1, A_rel' V_rel τ A0 A1 ->
            μ ρ0 e0 A0 = μ ρ1 e1 A1.

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

Definition A_rel := A_rel' V_rel.

Notation "'EREL' e0 , e1 ∈ E[ τ ]" :=
  (E_rel V_rel τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, τ at level 99).
Notation "'AREL' A0 , A1 ∈ A[ τ ]" :=
  (A_rel V_rel τ A0 A1)
    (at level 69, A0 at level 99, A1 at level 99, τ at level 99).


Record G_rel {Γ : Env Ty} {ρ0 ρ1 : Env Val} : Type :=
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

Definition dirac {A} (v : A) : Meas A :=
  fun e => Indicator e v.

Definition is_dirac {A} (v : A) (m : Meas A) : Prop :=
  m = dirac v.

Ltac decide_eval' ρ exp v w e u :=
  let not_ex := fresh "not_ex" in
  destruct (eval_dec ρ exp) as [[[v w] [e u]] | not_ex];
  [|
   try (contradict not_ex; eexists (_, _); repeat constructor; eassumption);
   try (nnr; simpl; ring)].
Tactic Notation "decide_eval" constr(ρ) "," uconstr(exp) "as"
       "[" ident(v) ident(w) ident(e) ident(u) "]"
  := (decide_eval' ρ exp v w e u).

Ltac congruence_μ := unfold μ; f_equal; extensionality σ.

Axiom int_const_entropy :
  forall (v : R+)
         (f : Entropy -> R+),
     (forall x, f x = v) ->
     Integration f μEntropy = v.

Lemma pure_is_atomic A e ρ :
  (fun σ => eval_in ρ (e_pure e) A σ) =
  (fun σ => option0 (Indicator A <$> eval_a ρ e)).
Proof.
  extensionality σ.
  unfold eval_in, ev, ew.
  decide_eval ρ, _ as [v w ex u]; simpl in *. {
    inversion ex; subst.
    nnr.
    unfold nnr_mult.
    simpl.
    rewrite Rmult_1_r.
    destruct e as [ ? | x ? | x ]; simpl in *; try (inversion H0; tauto).
    destruct (ρ x); inversion H0; auto.
  } {
    destruct e as [ ? | x ? | x ]; simpl in *;
try (contradict not_ex; eexists (_, _); constructor; simpl; eauto; fail).

    remember (ρ x).
    destruct o. {
      contradict not_ex; eexists (_, _); constructor; simpl; eauto.
    } {
      simpl.
      nnr.
      unfold nnr_mult.
      simpl.
      ring.
    }
  }
Qed.

Lemma eval_a_total_for_well_typed {Γ ρ e τ} :
  (ENV ρ ⊨ Γ) ->
  (TC Γ ⊢ e_pure e : τ) ->
  exists v, eval_a ρ e = Some v.
Proof.
  intros.
  inversion H; try (eexists; reflexivity).
  simpl.
  pose proof (env_val_models X x τ H1).
  destruct X0.
  exists x0.
  auto.
Qed.

Lemma pure_is_dirac {Γ ρ e τ} :
  (ENV ρ ⊨ Γ) ->
  (TC Γ ⊢ e_pure e : τ) ->
  exists v : Val,
    eval_a ρ e = Some v /\
    μ ρ (e_pure e) = dirac v.
Proof.
  intros Hρ He.
  destruct (eval_a_total_for_well_typed Hρ He).
  exists x.
  split; auto.

  extensionality A.
  unfold μ, dirac; simpl.
  rewrite pure_is_atomic.
  apply int_const_entropy; intro σ.
  rewrite H.
  simpl.
  auto.
Qed.

Lemma compat_real Γ r :
  (EXP Γ ⊢ e_pure (e_real r) ≈ e_pure (e_real r) : ℝ).
Proof.
  repeat constructor.
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  pose proof pure_is_dirac (G_rel_modeling0 Hρ) (TCReal r) as H0.
  pose proof pure_is_dirac (G_rel_modeling1 Hρ) (TCReal r) as H1.
  destruct H0 as [v0 [Hea0 Hdirac0]].
  destruct H1 as [v1 [Hea1 Hdirac1]].

  rewrite Hdirac0, Hdirac1.

  unfold dirac.
  unfold Indicator.
  f_equal.
  apply HA.
  simpl in Hea0, Hea1.
  injection Hea0.
  injection Hea1.
  intros.
  rewrite <- H, <- H0.
  simpl.
  auto.
Qed.

Lemma compat_var Γ x τ :
  Γ x = Some τ ->
  EXP Γ ⊢ e_pure (e_var x) ≈ e_pure (e_var x) : τ.
Proof.
  repeat constructor; auto.
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  pose proof pure_is_dirac (G_rel_modeling0 Hρ) (TCVar H) as H0.
  pose proof pure_is_dirac (G_rel_modeling1 Hρ) (TCVar H) as H1.
  destruct H0 as [v0 [Heval0 Hdirac0]].
  destruct H1 as [v1 [Heval1 Hdirac1]].

  rewrite Hdirac0, Hdirac1.
  unfold dirac.
  unfold Indicator.
  f_equal.
  apply HA.
  simpl in *.
  eapply G_rel_V; eauto.
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
  (EXP Γ ⊢ e_pure (e_lam x body0) ≈ e_pure (e_lam x body1) : (τa ~> τr)).
Proof.
  intros Hbody.
  repeat constructor; try apply Hbody.
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  destruct Hbody as [Hbody0 [Hbody1 ?]].

  pose proof pure_is_dirac (G_rel_modeling0 Hρ) (TCLam Hbody0) as H0.
  pose proof pure_is_dirac (G_rel_modeling1 Hρ) (TCLam Hbody1) as H1.
  destruct H0 as [v0 [Heval0 Hdirac0]].
  destruct H1 as [v1 [Heval1 Hdirac1]].

  rewrite Hdirac0, Hdirac1.
  unfold dirac.
  unfold Indicator.
  f_equal.
  apply HA.

  inversion Heval0.
  inversion Heval1.
  subst.

  intros va0 va1 Hva.
  apply H; auto.
  apply extend_grel; auto.
Qed.

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

Definition preimage {A B C} (f : A -> B) : (B -> C) -> (A -> C) :=
  fun eb a => eb (f a).

Lemma lemma_3 :
  forall {X}
         (M : Event X -> Event X -> Prop)
         (μ0 μ1 : Meas X)
         (μs_aggree : forall A0 A1, M A0 A1 -> μ0 A0 = μ1 A1)
         (f0 f1 : X -> R+)
         (f_is_M_measurable :
            forall (B : Event R+),
              M (preimage f0 B) (preimage f1 B)),
    Integration f0 μ0 = Integration f1 μ1.
Proof.
  intros.
  rewrite riemann_def_of_lebesgue_integration.
  apply eq_sym.
  rewrite riemann_def_of_lebesgue_integration.
  apply eq_sym.

  f_equal.
  extensionality t.
  apply μs_aggree.

  specialize (f_is_M_measurable (fun fx => bool_of_dec (fx [>] t))).
  unfold preimage in *.

  apply f_is_M_measurable.
Qed.

Axiom lemma_9 : forall (g : Entropy -> Entropy -> R+),
    Integration (fun σ => g (πL σ) (πR σ)) μEntropy =
    Integration (fun σL => Integration (fun σR => g σL σR) μEntropy) μEntropy.

Lemma pick_2_entropies : forall (g : Entropy -> Entropy -> R+),
    Integration (fun σ => g (π 0 σ) (π 1 σ)) μEntropy =
    Integration (fun σ0 => Integration (fun σ1 => g σ0 σ1) μEntropy) μEntropy.
Proof.
  intros.
  simpl.
  rewrite <- lemma_9.
Admitted.

Lemma pick_3_entropies : forall (g : Entropy -> Entropy -> Entropy -> R+),
    Integration (fun σ => g (π 0 σ) (π 1 σ) (π 2 σ)) μEntropy =
    Integration
      (fun σ0 =>
         Integration
           (fun σ1 =>
              Integration
                (fun σ2 =>
                   g σ0 σ1 σ2)
                μEntropy)
           μEntropy)
      μEntropy.
Proof.
Proof.
  intros.
  rewrite <- lemma_9.
  rewrite <- lemma_9.
  simpl.
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
    Integration (fun σ => option0 (f <$> ev ρ e σ) [*] ew ρ e σ) μEntropy.
Proof.
  intros.

  unfold μ.

  rewrite riemann_def_of_lebesgue_integration.
  rewrite lemma_1.
  unfold eval_in.

  match goal with
  | [ |- _ (fun y => _ (fun x => ?v [*] ?w) _) _ = _ ] =>
    assert ((fun y : Entropy => Integration (fun x => v [*] w) lebesgue_measure) =
            (fun y : Entropy => Integration (fun x => v) lebesgue_measure [*] w))
  end.
  {
    extensionality σ.
    rewrite <- Integration_linear_mult_r.
    auto.
  }
  rewrite H0.
  clear H0.

  f_equal.
  extensionality σ.

  generalize (ew ρ e σ) as w, (ev ρ e σ) as v.
  intros.

  f_equal.
  induction v; simpl. {
    pose proof @integration_of_indicator.
    unfold Indicator in *.
    rewrite H0.
    apply lebesgue_measure_interval.
  } {
    replace (fun _ => nnr_0) with (fun _ : R => nnr_0 [*] nnr_0)
      by (extensionality z; nnr; apply Rmult_0_l).
    rewrite <- Integration_linear_mult_r.
    nnr.
    apply Rmult_0_r.
  }
Qed.

Definition ensemble_of_event {X} : Event X -> Ensemble X :=
  fun A x => A x = true.

Definition at_most_one {A} (P : A -> Prop) :=
  forall x, P x -> (forall x', P x' -> x = x').

(* Lemma eval_a_at_most_one ρ e: *)
(*   at_most_one (fun v => EVAL_A ρ ⊢ e ⇓ v). *)
(* Proof. *)
(*   unfold at_most_one. *)
(*   intros v Hv v' Hv'. *)
(*   rewrite Hv in Hv'. *)
(*   inversion Hv'. *)
(*   auto. *)
(* Qed. *)

(* Lemma unfold_app_inside_eval_in *)
(*       (ρ : Env Val) *)
(*       (ef ea : Expr) *)
(*       (x : Var) *)
(*       (body : Expr) *)
(*       (ρ_clo : Env Val) *)
(*       (va : Val) *)
(*       (w0 w1 : R+) *)
(*       (ev_f : EVAL ρ, (π 0 σ) ⊢ ef ⇓ v_clo x body ρ_clo, w0) *)
(*       (ev_a : EVAL ρ, (π 1 σ) ⊢ ea ⇓ va, w1) *)
(*       (A : Event Val) *)
(*   : eval_in ρ (ef @ ea) A = *)
(*     eval_in (ρ_clo[x → va]) body A. *)
(* Proof. *)
(*   extensionality σ0. *)
(*   unfold eval_in, ev, ew. *)

(*   decide_eval ρ as [app_v app_w app_ex app_u]. { *)
(*     decide_eval (ρ_clo[x → va]) as [vr wr exr ur]. { *)
(*       pose proof app_u (_, _) (EApp _ _ ev_f ev_a exr). *)
(*       inversion H; subst. *)
(*       auto. *)
(*     } { *)
(*       contradict not_ex. *)
(*       exists (app_v, app_w). *)
(*       inversion app_ex; subst. *)

(*       rewrite ev_f in H1. *)
(*       inversion H1; subst. *)

(*       rewrite ev_a in H3. *)
(*       inversion H3; subst. *)

(*       auto. *)
(*     } *)
(*   } { *)
(*     decide_eval (ρ_clo[x → va]) as [vr0 wr0 exr0 ur0]; auto. { *)
(*       contradict not_ex. *)
(*       eexists (_, _). *)
(*       econstructor; eauto. *)
(*     } *)
(*   } *)
(* Qed. *)

Lemma option_map_compose {A B C} (f : B -> C) (g : A -> B) (o : option A) :
  f <$> (g <$> o) = (f ∘ g) <$> o.
Proof.
  destruct o; reflexivity.
Qed.

Definition plus_in (A : Event Val) (v v' : Val) : R+ :=
  match v, v' with
  | v_real r, v_real r' => Indicator A (v_real (r + r'))
  | _, _ => nnr_0
  end.

Lemma by_theorem_15_plus {ρ el er Γ} A :
  (TC Γ ⊢ el : ℝ) ->
  (TC Γ ⊢ er : ℝ) ->
  (ENV ρ ⊨ Γ) ->
    Integration (fun σ => eval_in ρ (e_plus el er) A σ) μEntropy =
    Integration (fun vl =>
    Integration (fun vr =>
                   plus_in A vl vr
                ) (μ ρ er)
                ) (μ ρ el).
Proof.
  intros Hel Her Hρ.

  rewrite (theorem_15 _ Hel); auto.

  replace (Integration _ μEntropy)
  with (Integration
          (fun σ0 =>
             Integration
               (fun σ1 =>
                  option0 (plus_in A <$> ev ρ el σ0 <*> ev ρ er σ1)
                  (* (option0 *)
                  (*   (Indicator A <$> eval_plus ρ el er σ0 σ1)) *)
                    [*] (ew ρ er σ1))
               μEntropy
               [*] (ew ρ el σ0))
          μEntropy). {
    f_equal.
    extensionality σ0.
    f_equal.
    unfold option_map, plus_in, ew, ev.
    decide_eval ρ, el as [v0 w0 ex0 u0]; simpl. {
      rewrite (theorem_15 _ Her); auto.
    } {
      rewrite <- Integration_linear_mult_l.
      nnr; simpl; ring.
    }
  } {
    evar (x : Entropy -> Entropy -> R+).
    replace (fun σ => eval_in ρ (e_plus el er) A σ)
    with (fun σ => x (π 0 σ) (π 1 σ)); subst x. {
      rewrite pick_2_entropies.
      f_equal.
      extensionality σ0.
      rewrite Integration_linear_mult_r.
      f_equal.
      extensionality σ1.
      reflexivity.
    } {
      extensionality σ.
      unfold eval_in, ev, ew.
      decide_eval ρ, (e_plus _ _) as [v0 w0 ex0 u0]; simpl. {
        inversion ex0; subst.
        decide_eval ρ, el as [v3 w3 ex3 u3]; simpl.
        decide_eval ρ, er as [v4 w4 ex4 u4]; simpl.

        pose proof (u3 (_, _) H1).
        pose proof (u4 (_, _) H4).
        inversion H; subst.
        inversion H0; subst.
        simpl.
        nnr; simpl; ring.
      } {
        decide_eval ρ, el as [v3 w3 ex3 u3].
        decide_eval ρ, er as [v4 w4 ex4 u4].
        destruct v3, v4; try (nnr; simpl; ring).
        contradict not_ex.
        eexists (_, _).
        constructor; eauto.
      }
    }
  }
Qed.

Lemma compat_plus Γ el0 er0 el1 er1 :
  (EXP Γ ⊢ el0 ≈ el1 : ℝ) ->
  (EXP Γ ⊢ er0 ≈ er1 : ℝ) ->
  (EXP Γ ⊢ e_plus el0 er0 ≈ e_plus el1 er1 : ℝ).
Proof.
  intros Hl Hr.
  destruct Hl as [tc_l0 [tc_l1 Hl]].
  destruct Hr as [tc_r0 [tc_r1 Hr]].
  repeat constructor; auto.
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  specialize (Hl _ _ Hρ).
  specialize (Hr _ _ Hρ).

  unfold μ.

  rewrite (by_theorem_15_plus _ tc_l0 tc_r0 (G_rel_modeling0 Hρ)).
  rewrite (by_theorem_15_plus _ tc_l1 tc_r1 (G_rel_modeling1 Hρ)).

  apply (lemma_3 (A_rel ℝ)). {
    intros.
    apply Hl; auto.
  } {
    intros.
    intros vl0 vl1 Hvl.
    unfold preimage.
    f_equal.

    apply (lemma_3 (A_rel ℝ)). {
      intros.
      apply Hr; auto.
    } {
      intros.
      intros vr0 vr1 Hvr.

      unfold preimage.
      f_equal.

      destruct vl0, vl1, vr0, vr1; try contradiction.

      simpl.
      rewrite Hvl, Hvr.
      unfold compose.
      unfold Indicator.
      f_equal.
      apply HA.
      simpl.
      reflexivity.
    }
  }
Qed.

Definition apply_in (A : Event Val) (σ : Entropy) (v v' : Val) : R+ :=
  match v with
  | v_clo x e ρ => eval_in (ρ[x → v']) e A σ
  | _ => nnr_0
  end.

Lemma by_theorem_15_app {ρ ef ea Γ τa τr} A :
  (TC Γ ⊢ ef : (τa ~> τr)) ->
  (TC Γ ⊢ ea : τa) ->
  (ENV ρ ⊨ Γ) ->
    Integration (fun σ => eval_in ρ (e_app ef ea) A σ) μEntropy =
    Integration (fun vf =>
    Integration (fun va =>
    Integration (fun σ2 =>
                   apply_in A σ2 vf va
                ) μEntropy
                ) (μ ρ ea)
                ) (μ ρ ef).
Proof.
  intros Hef Hea Hρ.

  rewrite (theorem_15 _ Hef); auto.

  replace (Integration _ μEntropy)
  with (Integration
          (fun σ0 =>
             Integration
               (fun σ1 =>
                  Integration
                    (fun σ2 =>
                       option0 (apply_in A σ2 <$> ev ρ ef σ0 <*> ev ρ ea σ1))
                    μEntropy
                    [*] ew ρ ea σ1)
               μEntropy
               [*] ew ρ ef σ0)
          μEntropy). {
    f_equal.
    extensionality σ0.
    f_equal.
    unfold option_map, ew, ev.
    decide_eval ρ, ef as [v0 w0 ex0 u0]; simpl. {
      rewrite (theorem_15 _ Hea); auto.
      f_equal.
      extensionality σ1.

      unfold ev, ew, option_map.
      decide_eval ρ, ea as [v1 w1 ex1 u1]; simpl; auto.
    } {
      rewrite <- Integration_linear_mult_l.
      rewrite (int_const_entropy nnr_0); auto.
      nnr; simpl; ring.
    }
  } {
    evar (x : Entropy -> Entropy -> Entropy -> R+).
    replace (fun σ => eval_in ρ (e_app ef ea) A σ)
    with (fun σ => x (π 0 σ) (π 1 σ) (π 2 σ)); subst x. {
      rewrite pick_3_entropies.
      f_equal.
      extensionality σ0.
      rewrite Integration_linear_mult_r.
      f_equal.
      extensionality σ1.
      rewrite 2 Integration_linear_mult_r.
      f_equal.
      reflexivity.
    } {
      extensionality σ.
      unfold eval_in, ev, ew.
      decide_eval ρ, (e_app _ _) as [v0 w0 ex0 u0]; simpl. {
        inversion ex0; subst.
        decide_eval ρ, ef as [v4 w4 ex4 u4]; simpl.
        decide_eval ρ, ea as [v5 w5 ex5 u5]; simpl.

        pose proof (u4 (_, _) H1).
        pose proof (u5 (_, _) H2).
        inversion H; subst.
        inversion H0; subst.
        simpl.

        replace (Indicator _ _ [*] _)
        with ((Indicator A v0 [*] w3) [*] w2 [*] w1)
          by (nnr; simpl; ring).

        do 2 f_equal.

        unfold eval_in, ev, ew.
        decide_eval (ρ_clo[x → v1]), body as [v6 w6 ex6 u6].
        pose proof (u6 (_, _) H5).
        inversion H3; subst.
        auto.
      } {
        decide_eval ρ, ef as [v3 w3 ex3 u3].
        decide_eval ρ, ea as [v4 w4 ex4 u4].
        destruct v3 as [|x body ρ_clo]; try (nnr; simpl; ring).
        simpl.
        unfold apply_in, eval_in, ev, ew.
        decide_eval (ρ_clo[x → v4]), _ as [v5 w5 ex5 u5].
        contradict not_ex.
        eexists (_, _).
        econstructor; eauto.
      }
    }
  }
Qed.

Lemma compat_app Γ ef0 ef1 ea0 ea1 τa τr :
  (EXP Γ ⊢ ef0 ≈ ef1 : (τa ~> τr)) ->
  (EXP Γ ⊢ ea0 ≈ ea1 : τa) ->
  (EXP Γ ⊢ e_app ef0 ea0 ≈ e_app ef1 ea1 : τr).
Proof.
  intros Hf Ha.
  destruct Hf as [TCf0 [TCf1 Hf]].
  destruct Ha as [TCa0 [TCa1 Ha]].
  repeat econstructor; eauto.

  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  specialize (Hf _ _ Hρ).
  specialize (Ha _ _ Hρ).

  unfold μ.

  rewrite (by_theorem_15_app _ TCf0 TCa0 (G_rel_modeling0 Hρ)).
  rewrite (by_theorem_15_app _ TCf1 TCa1 (G_rel_modeling1 Hρ)).

  apply (lemma_3 (A_rel (τa ~> τr))). {
    intros.
    apply Hf; auto.
  } {
    intros.
    intros vf0 vf1 Hvf.
    unfold preimage.
    f_equal.

    apply (lemma_3 (A_rel τa)). {
      intros.
      apply Ha; auto.
    } {
      intros.
      intros va0 va1 Hva.
      unfold preimage.
      f_equal.

      destruct vf0 as [|x0 body0 ρ_clo0], vf1 as [|x1 body1 ρ_clo1];
try contradiction.

      unfold apply_in.
      change (μ (ρ_clo0[x0 → va0]) body0 A0 = μ (ρ_clo1[x1 → va1]) body1 A1).
      apply Hvf; auto.
    }
  }
Qed.

Lemma compat_sample Γ :
  EXP Γ ⊢ e_sample ≈ e_sample : ℝ.
Proof.
  repeat constructor.
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  congruence_μ.

  pose proof ESample ρ0 σ as EVAL_0.
  pose proof ESample ρ1 σ as EVAL_1.

  unfold eval_in, ev, ew.

  decide_eval ρ0, _ as [v0 w0 e0 u0].
  decide_eval ρ1, _ as [v1 w1 e1 u1].
  injection (u0 (_, _) EVAL_0); intros.
  injection (u1 (_, _) EVAL_1); intros.
  subst.

  simpl.
  unfold Indicator.
  do 2 f_equal.
  apply HA.
  simpl.
  reflexivity.
Qed.

Definition factor_in (A : Event Val) (v : Val) : R+ :=
  match v with
  | v_real r =>
    match Rle_dec 0 r with
    | left rpos => Indicator A (v_real r) [*] mknnr r rpos
    | _ => nnr_0
    end
  | _ => nnr_0
  end.

Lemma by_theorem_15_factor {ρ e Γ} A :
  (TC Γ ⊢ e : ℝ) ->
  (ENV ρ ⊨ Γ) ->
    Integration (fun σ => eval_in ρ (e_factor e) A σ) μEntropy =
    Integration (factor_in A) (μ ρ e).
Proof.
  intros He Hρ.
  rewrite (theorem_15 _ He); auto.

  f_equal.
  extensionality σ.
  unfold option_map, factor_in, eval_in, ev, ew.

  decide_eval ρ, (e_factor e) as [v0 w0 ex0 u0]. {
    inversion ex0.
    subst.
    decide_eval ρ, e as [v1 w1 ex1 u1]. {
      simpl.
      injection (u1 (_, _) H0); intros.
      subst.
      destruct Rle_dec. {
        nnr; simpl; ring.
      } {
        contradict n; auto.
      }
    }
  } {
    simpl.
    decide_eval ρ, e as [v1 w1 ex1 u1]. {
      simpl.
      destruct v1. {
        destruct Rle_dec. {
          contradict not_ex.
          eexists (v_real r, _).
          eapply EFactor with (rpos := r0).
          eauto.
        } {
          nnr; simpl; ring.
        }
      } {
        nnr; simpl; ring.
      }
    }
  }
Qed.

Lemma compat_factor Γ e0 e1:
  (EXP Γ ⊢ e0 ≈ e1 : ℝ) ->
  (EXP Γ ⊢ e_factor e0 ≈ e_factor e1 : ℝ).
Proof.
  intro He.
  destruct He as [TC0 [TC1 He]].
  repeat constructor; auto.
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  specialize (He _ _ Hρ).

  unfold μ.

  rewrite (by_theorem_15_factor _ TC0 (G_rel_modeling0 Hρ)).
  rewrite (by_theorem_15_factor _ TC1 (G_rel_modeling1 Hρ)).

  apply (lemma_3 (A_rel ℝ)). {
    intros.
    apply He; auto.
  } {
    intros.
    intros v0 v1 Hv.
    unfold preimage.
    f_equal.

    unfold factor_in.
    destruct v0; try contradiction.
    destruct v1; try contradiction.
    simpl in Hv.
    rewrite Hv.
    destruct Rle_dec; auto.
    unfold Indicator.
    do 2 f_equal.
    apply HA.
    simpl.
    auto.
  }
Qed.

Lemma fundamental_properties Γ e τ :
  (TC Γ ⊢ e : τ) ->
  (EXP Γ ⊢ e ≈ e : τ).
Proof.
  intros.
  induction H.
  - apply compat_real.
  - apply compat_var; tauto.
  - apply compat_lam; tauto.
  - apply compat_app with (τa := τa); tauto.
  - apply compat_factor; tauto.
  - apply compat_sample.
  - apply compat_plus; tauto.
Qed.

Print Assumptions fundamental_properties.
