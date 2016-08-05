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
Notation "ρ [ x → v ]" := (extend ρ x v) (at level 68, left associativity).

Reserved Notation "'TC' Γ ⊢ e : τ" (at level 70, e at level 99, no associativity).
Inductive tc {Γ : Env Ty} : Expr -> Ty -> Prop :=
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
where "'TC' Γ ⊢ e : τ" := (tc (Γ := Γ) e τ)
.

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

Fixpoint π (n : nat) (σ : Entropy) : Entropy :=
  match n with
  | O => πL σ
  | S n' => π n' (πR σ)
  end.

Reserved Notation "'EVAL' ρ , σ ⊢ e ⇓ v , w" (at level 69, e at level 99, no associativity).
Inductive eval (ρ : Env Val) : Entropy -> Expr -> Val -> R -> Type :=
| EVar (σ : Entropy) {x : Var} {v : Val}
  : ρ x = Some v ->
    EVAL ρ, σ ⊢ `x ⇓ v, 1
| EReal (σ : Entropy) (r : R)
  : EVAL ρ, σ ⊢ e_real r ⇓ v_real r, 1
| ELam (σ : Entropy) (x : Var) (τ : Ty) (e : Expr)
  : EVAL ρ, σ ⊢ λ x ; τ , e ⇓ v_clo x e ρ, 1
| EPlus (σ : Entropy) (e0 e1 : Expr) (r0 r1 : R) (w0 w1 : R)
  : (EVAL ρ, (π 0 σ) ⊢ e0 ⇓ v_real r0, w0) ->
    (EVAL ρ, (π 1 σ) ⊢ e1 ⇓ v_real r1, w1) ->
    EVAL ρ, σ ⊢ e_plus e0 e1 ⇓ v_real (r0 + r1), w0 * w1
| EApp (σ : Entropy) (e0 e1 : Expr)
       (x : Var) (body : Expr) (ρ_clo : Env Val)
       (v1 v2 : Val)
       (w0 w1 w2 : R)
  : EVAL ρ, (π 0 σ) ⊢ e0 ⇓ v_clo x body ρ_clo, w0 ->
    EVAL ρ, (π 1 σ) ⊢ e1 ⇓ v1, w1 ->
    EVAL (ρ_clo[x → v1]), (π 2 σ) ⊢ body ⇓ v2, w2 ->
    EVAL ρ, σ ⊢ e0 @ e1 ⇓ v2, w0 * w1 * w2
| ESample (σ : Entropy)
  : EVAL ρ, σ ⊢ e_sample ⇓ v_real (proj1_sig (σ 0%nat)), 1
| EFactor (σ : Entropy) (e : Expr) (r w : R)
  : r > 0 ->
    EVAL ρ, σ ⊢ e ⇓ v_real r, w ->
    EVAL ρ, σ ⊢ e_factor e ⇓ v_real r, r * w
where "'EVAL' ρ , σ ⊢ e ⇓ v , w" := (eval ρ σ e v w)
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
    (existsT! vw : (Val * R), let (v, w) := vw in EVAL ρ, σ ⊢ e ⇓ v, w) +
    ((existsT vw : (Val * R), let (v, w) := vw in EVAL ρ, σ ⊢ e ⇓ v, w) -> False).

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

Definition A_rel' (V_rel : Ty -> Val -> Val -> Type) (τ : Ty) (A : Event Val) :=
  forall v0 v1,
    V_rel τ v0 v1 ->
    (A v0 = A v1).

Definition E_rel' (V_rel : Ty -> Val -> Val -> Type) (τ : Ty) (c0 c1 : Config) :=
  let (ρ0, e0) := c0 in
  let (ρ1, e1) := c1 in
  forall A, A_rel' V_rel τ A ->
            μ ρ0 e0 A = μ ρ1 e1 A.

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
                    E_rel' V_rel τr
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
Definition E_rel := E_rel' V_rel.
Notation "'EREL' e0 , e1 ∈ E[ τ ]" :=
  (E_rel τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, τ at level 99).
Definition A_rel := A_rel' V_rel.
Notation "'AREL' v0 , v1 ∈ E[ τ ]" :=
  (A_rel τ v0 v1)
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

(* this won't be true without a real definition of contexts *)
Definition obs_equiv (e1 e2 : Expr) :=
  forall (C : Expr -> Expr) (A : Event Val),
    μ empty_env (C e1) A = μ empty_env (C e2) A.
Notation "e0 '=ctx' e1" := (obs_equiv e0 e1) (at level 60, no associativity).

Ltac split3 := split; [|split].
Ltac decompose_common b :=
  let H := fresh "H" in
  pose proof b as H;
  hnf in H;
  decompose [ex sum and sig sigT G_rel @env_models prod] H;
  clear H.
(* absurdly common typo I'm sick of correcting *)
Ltac inductino a := induction a.
Ltac murder_eq xs :=
  let m x :=
      match goal with
      | [ H : x = _ |- _ ] => (try rewrite H in *); clear x H
| [ H : _ = x |- _ ] => (try rewrite <- H in *); clear x H
end in
  match xs with
    (* I hate ltac *)
  | ?a => m a
  | (?a, ?b) => m a; m b
  | (?a, ?b, ?c) => m a; m b; m c
  | (?a, ?b, ?c, ?d) => m a; m b; m c; m d
  | (?a, ?b, ?c, ?d, ?e) => m a; m b; m c; m d; m e
  | (?a, ?b, ?c, ?d, ?e, ?f) => m a; m b; m c; m d; m e; m f
  | (?a, ?b, ?c, ?d, ?e, ?f, ?g) => m a; m b; m c; m d; m e; m f; m g
  | (?a, ?b, ?c, ?d, ?e, ?f, ?g, ?h) => m a; m b; m c; m d; m e; m f; m g; m h
  | (?a, ?b, ?c, ?d, ?e, ?f, ?g, ?h, ?i) => m a; m b; m c; m d; m e; m f; m g; m h; m i
  end.

Lemma compat_const_real Γ r :
  EXP Γ ⊢ e_real r ≈ e_real r : ℝ.
Proof.
  split3; try apply TCReal.
  intros.
  intro A.
  intros.
  unfold μ.
  apply f_equal2; auto.
  extensionality σ.
  unfold evalin, ev, ew.
  induction (eval_dec ρ0 (e_real r) σ), (eval_dec ρ1 (e_real r) σ); try ring. {
    induction a, p, x, s, u, x.
    inversion y.
    inversion y0.
    auto.
  } {
    contradict f.
    exists (v_real r, 1).
    apply EReal.
  } {
    contradict b.
    exists (v_real r, 1).
    apply EReal.
  }
Qed.

Lemma compat_var Γ x τ :
  Γ x = Some τ ->
  EXP Γ ⊢ `x ≈ `x : τ.
Proof.
  intros.
  split3; try apply TCVar; auto.
  unfold E_rel, E_rel'.
  intros.
  unfold μ.
  induction (env_val_models (G_rel_modeling0 X) x τ H) as [v0 Hv0].
  induction (env_val_models (G_rel_modeling1 X) x τ H) as [v1 Hv1].
  pose proof (G_rel_V X) H Hv0 Hv1.

  apply f_equal2; auto.
  extensionality σ.

  unfold evalin, ev, ew.
  pose proof (EVar ρ0 σ Hv0) as E0.
  pose proof (EVar ρ1 σ Hv1) as E1.
  induction eval_dec. {
    induction a, x0, p.
    injection (e0 (_, _) E0); intros.

    induction eval_dec. {
      induction a, x0, p.
      injection (e2 (_, _) E1); intros.
      rewrite H2, H3, H4, H5 in *.
      replace (A v1) with (A v0) by (apply H0; auto).
      reflexivity.
    } {
      contradict b.
      exists (v1, 1).
      exact (EVar _ _ Hv1).
    }
  } {
    contradict b.
    exists (v0, 1).
    exact (EVar _ _ Hv0).
  }
Qed.

Lemma stupid_is_stupid :
  forall v0 v1 : Val, None = Some v0 <-> None = Some v1.
Proof.
  intros.
  split; intro stupid; inversion stupid.
Qed.

Lemma compat_lam Γ x body0 body1 τa τr :
  (EXP Γ[x → τa] ⊢ body0 ≈ body1 : τr) ->
  (EXP Γ ⊢ λ x ; τa, body0 ≈ λ x ; τa, body1 : (τa ~> τr)).
Proof.
  intros.
  destruct H as [TC0 [TC1 H]].
  split3; try (apply TCLam; assumption).
  intros.
  intros A HA.

  unfold μ.
  apply f_equal2; auto.
  extensionality σ.
  unfold evalin, ev, ew.

  pose proof (ELam ρ0 σ x τa body0) as E0.
  pose proof (ELam ρ1 σ x τa body1) as E1.

  destruct (eval_dec ρ0) as [[[v0 r0] [e0 u0]] | not_ex]. {
    destruct (eval_dec ρ1) as [[[v1 r1] [e1 u1]] | not_ex]. {
      injection (u0 (_, _) E0); intros tH0a tH0b.
      injection (u1 (_, _) E1); intros tH1a tH1b.
      rewrite tH0a, tH0b, tH1a, tH1b in *.
      clear tH0a tH0b tH1a tH1b r0 v0 r1 v1 u0 u1 e0 e1.
      replace (A (v_clo x body1 ρ1)) with (A (v_clo x body0 ρ0)); [reflexivity|].

      apply HA.
      simpl.
      intros.
      apply H; auto.
      split;
try split;
intro x';
unfold extend;
induction Var_eq_dec;
try (split; intro stupid; inversion stupid; fail);
try apply X;
try (eexists; trivial).

      intros.
      inversion H2.
      inversion H3.
      inversion H4.
      rewrite <- H6, <- H7, <- H8.
      assumption.
    }
    contradict not_ex.
    eexists (_, _).
    exact E1.
  } {
    contradict not_ex.
    eexists (_, _).
    exact E0.
  }
Qed.

Axiom lemma_9 : forall (g : Entropy -> Entropy -> R),
    Integration (fun σ => g (πL σ) (πR σ)) μEntropy =
    Integration (fun σ2 => Integration (fun σ1 => g σ1 σ2) μEntropy) μEntropy.

Lemma its_just_the_definition_of_applyin_how_hard_could_it_be :
  forall
  (ef ea : Expr)
  (ρ : Env Val)
  (A : Event Val),
    (fun σ => evalin ρ (ef @ ea) A σ) =
    (fun σ => applyin
                (ev ρ ef (π 0 σ))
                (ev ρ ea (π 1 σ))
                A
                (π 2 σ)
              * ew ρ ef (π 0 σ)
              * ew ρ ea (π 1 σ)).
Proof.
  intros.
  extensionality σ.
  unfold applyin, evalin, ev, ew.
  destruct (eval_dec ρ ef) as [[[vf rf] [Ef uf]] | not_ex]. {
    destruct (eval_dec ρ ea) as [[[va ra] [Ea ua]] | not_ex]. {
      destruct (eval_dec ρ (ef @ ea)) as [[[v r] [E u]] | not_ex]. {
        inversion E.
        pose proof uf (_, _) X as uf.
        pose proof ua (_, _) X0 as ua.
        inversion uf.
        inversion ua.
        rewrite H5, H6, H7, H8 in *.
        clear H5 H6 H7 H8 vf rf va ra.
        replace ((if A v then 1 else 0) * (w0 * w1 * w2))
        with (((if A v then 1 else 0) * w2) * w0 * w1). {
          apply f_equal2; auto.
          apply f_equal2; auto.

          destruct eval_dec as [[[vr rr] [Er ur]] | not_ex]. {
            pose proof ur (_, _) X1.
            inversion H4.
            reflexivity.
          } {
            contradict not_ex.
            eexists (_, _).
            exact X1.
          }
        } {
          generalize (if A v then 1 else 0).
          intro.
          repeat rewrite Rmult_assoc.
          apply f_equal2; auto.
          rewrite <- Rmult_comm.
          rewrite Rmult_assoc.
          auto.
        }
      } {
        induction vf as [| x body ρ_clo|]. {
          repeat rewrite Rmult_0_l; auto.
        } {
          destruct eval_dec as [[[vr rr] [Er ur]] | not_ex2]. {
            contradict not_ex.
            eexists (_, _).
            eapply EApp.
            exact Ef.
            exact Ea.
            exact Er.
          } {
            repeat rewrite Rmult_0_l; auto.
          }
        } {
            repeat rewrite Rmult_0_l; auto.
        }
      }
    } {
      rewrite Rmult_0_r.
      destruct eval_dec as [[[vr rr] [Er ur]] | not_ex2]. {
        inversion Er.
        contradict not_ex.
        eexists (_, _).
        exact X0.
      } {
        rewrite Rmult_0_r; auto.
      }
    }
  } {
    repeat rewrite Rmult_0_l.
    destruct eval_dec as [[[vr rr] [Er ur]] | not_ex2]. {
      inversion Er.
      contradict not_ex.
      eexists (_, _).
      exact X.
    } {
      rewrite Rmult_0_r; auto.
    }
  }
Qed.

Definition ent_lift {A} (f : Entropy -> A) : Entropy -> Entropy -> A :=
  fun σL σR => f (Ejoin σL σR).

Lemma ent_lift_same {A} (f : Entropy -> A) σ :
  ent_lift f (πL σ) (πR σ) = f σ.
Proof.
  unfold ent_lift, πL, πR.
  rewrite join_inv_split.
  auto.
Qed.

Lemma its_just_applying_lemma_9_how_hard_could_it_be :
  forall
  (ef ea : Expr)
  (ρ : Env Val)
  (A : Event Val),
    let f σ0 σ1 σ2 :=
        applyin (ev ρ ef σ0) (ev ρ ea σ1) A σ2
        * ew ρ ef σ0
        * ew ρ ea σ1
    in
    Integration (fun σ => f (π 0 σ) (π 1 σ) (π 2 σ)) μEntropy =
    Integration (fun σ2 =>
    Integration (fun σ1 =>
    Integration (fun σ0 =>
                   f σ0 σ1 σ2
                ) μEntropy
                ) μEntropy
                ) μEntropy.
Proof.
  intros.

  assert
    (Integration (fun σ => f (π 0 σ) (π 1 σ) (π 2 σ)) μEntropy =
     Integration (fun σ3 =>
     Integration (fun σ2 =>
     Integration (fun σ1 =>
     Integration (fun σ0 =>
                    f σ0 σ1 σ2
                 ) μEntropy
                 ) μEntropy
                 ) μEntropy
                 ) μEntropy).
  {
    simpl.
    repeat rewrite <- lemma_9.
    trivial.
  } {
    rewrite H.
    erewrite int_const_entropy.
    reflexivity.
    auto.
  }
Qed.

Definition meas_lift {A} (m : Meas A) : Meas (option A) :=
  {| Meas_fn := fun p => Meas_fn m (fun a => p (Some a)) |}.

Axiom theorem_15 :
  forall (f : option Val -> R) {Γ e τ ρ},
    (TC Γ ⊢ e : τ) ->
    (ENV Γ ⊨ ρ) ->
    Integration f (meas_lift {| Meas_fn := μ ρ e |}) =
    Integration (fun σ => f (ev ρ e σ) * ew ρ e σ) μEntropy.

Lemma its_just_applying_theorem_15_how_hard_could_it_be :
  forall
  {ef ea : Expr}
  Γ τa τr
  (tcf : TC Γ ⊢ ef : τa ~> τr)
  (tca : TC Γ ⊢ ea : τa)
  (ρ : Env Val)
  (env_models : ENV Γ ⊨ ρ)
  (A : Event Val),
    let f σ0 σ1 σ2 :=
        applyin (ev ρ ef σ0) (ev ρ ea σ1) A σ2
        * ew ρ ef σ0
        * ew ρ ea σ1
    in
    Integration (fun σ2 =>
    Integration (fun σ1 =>
    Integration (fun σ0 =>
                   f σ0 σ1 σ2
                ) μEntropy
                ) μEntropy
                ) μEntropy =
    Integration (fun σ2 =>
    Integration (fun va =>
    Integration (fun vf =>
                   applyin vf va A σ2
                ) (meas_lift {| Meas_fn := μ ρ ef |})
                ) (meas_lift {| Meas_fn := μ ρ ea |})
                ) μEntropy.
Proof.
  intros.
  apply f_equal2; auto.
  extensionality σ2.
  rewrite theorem_15 with (Γ := Γ) (τ := τa); auto.
  apply f_equal2; auto.
  extensionality σ1.
  rewrite theorem_15 with (Γ := Γ) (τ := τa ~> τr); auto.
  rewrite Rmult_comm.
  rewrite Integration_linear.
  apply f_equal2; auto.
  extensionality σ0.
  subst f.
  simpl.
  apply Rmult_comm.
Qed.

Definition preimage {A B R} (f : A -> B) : (B -> R) -> (A -> R) :=
  fun eb a => eb (f a).

Definition ensemble_of_event {X} : Event X -> Ensemble X :=
  fun A x => A x = true.

Axiom lemma_3 :
  forall {X}
         (M : Ensemble (Event X))
         (μ1 μ2 : Meas X)
         (μs_aggree : forall A, M A ->
                                Meas_fn μ1 A = Meas_fn μ2 A)
         (f : X -> R)
         (f_is_M_measurable :
            forall (B : R -> bool),
              M (preimage f B)),
    Integration f μ1 = Integration f μ2.

Axiom product_measure : forall {A B} (μA : Meas A) (μB : Meas B), Meas (A * B).
Axiom product_measure_integration :
  forall {A B} (μA : Meas A) (μB : Meas B) f,
    Integration (fun x => Integration (fun y => f x y) μB) μA =
    Integration (fun xy => f (fst xy) (snd xy)) (product_measure μA μB).

Axiom product_measure_eq_on_rectangles_is_eq :
  forall {A B} (μA0 μA1 : Meas A) (μB0 μB1 : Meas B),
    (forall (X : Event A) (Y : Event B),
        Meas_fn μA0 X * Meas_fn μB0 Y = Meas_fn μA1 X * Meas_fn μB1 Y) ->
    product_measure μA0 μB0 =
    product_measure μA1 μB1.


Definition rectangle {A B} (X : Event A) (Y : Event B) : Event (A * B) :=
  fun ab => (X (fst ab) && Y (snd ab))%bool.

Axiom product_measure_on_rectangle :
  forall {A B} (μA : Meas A) (μB : Meas B)
         (X : Event A) (Y : Event B),
    Meas_fn (product_measure μA μB) (rectangle X Y) = Meas_fn μA X * Meas_fn μB Y.

Definition a_product_rel (M0 : Ensemble (Event Val)) :
  Ensemble (Event (option Val * option Val)) :=
  fun (x : Event (option Val * option Val)) =>
    M0 (fun v : Val =>
          match v with
          | v_pair va ((v_clo _ _ _) as vf) => x (Some va, Some vf)
          | _ => false
          end).

Lemma apply_product_measure_integration :
  forall {X Y AT} (μa : Meas X) (μf : Meas Y) (A : AT) f,
   Integration
     (fun σ2 =>
        Integration
          (fun va => Integration (fun vf => f vf va A σ2) μa) μf)
     μEntropy =
   Integration
     (fun σ2 =>
        Integration
          (fun vavf => f (snd vavf) (fst vavf) A σ2) (product_measure μf μa))
     μEntropy.
Proof.
  intros.
  apply f_equal2; auto.
  extensionality σ2.
  rewrite product_measure_integration.
  trivial.
Qed.

Lemma apply_lemma_3 :
  Integration
    (fun σ2 : Entropy =>
       Integration (fun vavf => applyin (snd vavf) (fst vavf) A σ2) μ0)
    μEntropy =
  Integration
    (fun σ2 : Entropy =>
       Integration (fun vavf => applyin (snd vavf) (fst vavf) A σ2) μ1)
    μEntropy.
Proof.
  intros.
  apply f_equal2; auto.
  extensionality σ2.
  rewrite (lemma_3 (a_product_rel (A_rel (τa ⨉ (τa ~> τr)))) μ0 μ1); auto.
Qed.

Lemma compat_app Γ ef0 ef1 ea0 ea1 τa τr :
  (EXP Γ ⊢ ef0 ≈ ef1 : (τa ~> τr)) ->
  (EXP Γ ⊢ ea0 ≈ ea1 : τa) ->
  (EXP Γ ⊢ ef0 @ ea0 ≈ ef1 @ ea1 : τr).
Proof.
  intros Hf Ha.
  destruct Hf as [TCf0 [TCf1 Hf]].
  destruct Ha as [TCa0 [TCa1 Ha]].
  split3; try (apply TCApp with (τa0 := τa); assumption).

  intros.
  intros A HA.

  pose proof (Hf ρ0 ρ1 X) as agree_on_arrow.
  pose proof (Ha ρ0 ρ1 X) as agree_on_arg.
  clear Hf Ha (* TCf0 TCf1 TCa0 TCa1 *).

  unfold E_rel, E_rel' in *.

  unfold μ.

  rewrite 2 its_just_the_definition_of_applyin_how_hard_could_it_be.
  rewrite 2 its_just_applying_lemma_9_how_hard_could_it_be.
  rewrite 2 (its_just_applying_theorem_15_how_hard_could_it_be Γ τa τr);
try apply X;
auto.

  set (μa0 := meas_lift _).
  set (μf0 := meas_lift _).
  set (μa1 := meas_lift _).
  set (μf1 := meas_lift _).

  rewrite 2 apply_product_measure_integration.

  set (μ1 := product_measure _ _).
  set (μ2 := product_measure _ _).

  apply (apply_lemma_3 τa τr). {
  (* rewrite (lemma_3 (a_product_rel (A_rel (τa ⨉ (τa ~> τr))))). { *)
    intros.
    subst μ1 μ2.

    unfold a_product_rel in H.
    unfold A_rel, A_rel' in H.

    admit.
  } {
    intros.
    unfold preimage.
    unfold a_product_rel.
    intros v0 v1 vrel.
    destruct
      v0 as [| | va0 [| x0 body0 ρ_clo0 |]],
            v1 as [| | va1 [| x1 body1 ρ_clo1 |]];
trivial;
inversion vrel;
try inversion H0.

    simpl.
    apply f_equal.
    clear B.

    pose proof H0 _ _ H _ HA as H0.
    simpl in H1.


  }
Qed.

Lemma compat_plus Γ el0 er0 el1 er1 :
  (EXP Γ ⊢ el0 ≈ el1 : ℝ) ->
  (EXP Γ ⊢ er0 ≈ er1 : ℝ) ->
  (EXP Γ ⊢ e_plus el0 er0 ≈ e_plus el1 er1 : ℝ).
Proof.
  intros.
  induction H, H0, H1, H2.
  split3; try (apply TCPlus; assumption).
  intros.
  pose proof (H3 _ _ X).
  pose proof (H4 _ _ X).
  intros A HA.
Admitted.

Lemma compat_sample Γ :
  EXP Γ ⊢ e_sample ≈ e_sample : ℝ.
Proof.
  split3; try apply TCSample.
  intros.
  intros A HA.

  unfold μ.
  apply f_equal2; auto.
  extensionality σ.

  pose proof ESample ρ0 σ as E0.
  pose proof ESample ρ1 σ as E1.

  unfold evalin, ev, ew.

  destruct (eval_dec ρ0) as [[[v0 r0] [e0 u0]] | not_ex]. {
    destruct (eval_dec ρ1) as [[[v1 r1] [e1 u1]] | not_ex]. {
      injection (u0 (_, _) E0); intros.
      injection (u1 (_, _) E1); intros.
      rewrite H, H0, H1, H2 in *.
      reflexivity.
    } {
      contradict not_ex.
      eexists (_, _).
      exact E1.
    }
  } {
    contradict not_ex.
    eexists (_, _).
    exact E0.
  }
Qed.

Lemma compat_factor Γ e0 e1:
  (EXP Γ ⊢ e0 ≈ e1 : ℝ) ->
  (EXP Γ ⊢ e_factor e0 ≈ e_factor e1 : ℝ).
Proof.
  intro H.
  destruct H as [TC0 [TC1 H]].
  split3; try (apply TCFactor; assumption).
  intros.
  pose proof H ρ0 ρ1 X.
  clear H.

  intros A HA.

  unfold μ.
  apply f_equal2; auto.
  extensionality σ.

  pose proof (H0 A HA).
Admitted.

Lemma funamental_property Γ e τ :
  (TC Γ ⊢ e : τ) ->
  (EXP Γ ⊢ e ≈ e : τ).
Proof.
  intros.
  induction H.
  - apply compat_const_real.
  - apply compat_var; assumption.
  - apply compat_lam; assumption.
  - apply compat_app with (τa := τa); assumption.
  - apply compat_plus; assumption.
  - apply compat_sample.
  - apply compat_factor; assumption.
Qed.
