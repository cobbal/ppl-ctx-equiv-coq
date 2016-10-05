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

Definition Var := nat.
Definition Var_eq_dec : forall x y : Var, {x = y} + {x <> y} := Nat.eq_dec.

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
| e_pure : AExpr -> Expr
with AExpr :=
| e_real : R -> AExpr
| e_lam : Ty -> Expr -> AExpr
| e_var : Var -> AExpr
.

Scheme Expr_AExpr_rect := Induction for Expr Sort Type
with
AExpr_Expr_rect := Induction for AExpr Sort Type.

Definition Env (T : Type) := list T.
Definition empty_env {T : Type} : Env T := nil.
Definition extend {T} (ρ : Env T) (v : T) : Env T :=
  v :: ρ.
Fixpoint lookup {T} (ρ : Env T) x : option T :=
  match x, ρ with
  | _, nil => None
  | O, (v :: _) => Some v
  | S x', (_ :: ρ') => lookup ρ' x'
  end.

Reserved Notation "'TC' Γ ⊢ e : τ" (at level 70, e at level 99, no associativity).
Inductive tc {Γ : Env Ty} : Expr -> Ty -> Type :=
| TCReal (r : R)
  : (TC Γ ⊢ e_pure (e_real r) : ℝ)
| TCVar {x : Var} {τ : Ty}
  : lookup Γ x = Some τ ->
    (TC Γ ⊢ e_pure (e_var x) : τ)
| TCLam {τa τr : Ty} {body : Expr}
  : (TC (extend Γ τa) ⊢ body : τr) ->
    (TC Γ ⊢ e_pure (e_lam τa body) : τa ~> τr)
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
| v_clo : Ty -> Expr -> Env Val -> Val
.

(* Print Val_rect. *)
Definition Val_Val_Env_rect
    (P : Val -> Type)
    (P0 : Env Val -> Type)
    (val_case_r :
       forall r : R,
         P (v_real r))
    (val_case_clo :
       forall (τ : Ty) (e : Expr) (ρ : Env Val),
         P0 ρ ->
         P (v_clo τ e ρ))
    (env_case_nil : P0 nil)
    (env_case_cons :
       forall (v : Val) (ρ' : Env Val),
         P v ->
         P0 ρ' ->
         P0 (v :: ρ'))
  : (forall v : Val, P v) :=
  fix fv v :=
    match v with
    | v_real r => val_case_r r
    | v_clo τ e ρ =>
      val_case_clo
        τ e ρ
        ((fix fρ ρ : P0 ρ :=
            match ρ with
            | nil => env_case_nil
            | (v :: ρ') => env_case_cons v ρ' (fv v) (fρ ρ')
            end) ρ)
    end.

(* Definition env_dom_eq {A B} (envA : Env A) (envB : Env B) := *)
(*   forall x, lookup envA x = None <-> lookup envB x = None. *)

Definition env_dom_eq {A B} (envA : Env A) (envB : Env B) :=
  length envA = length envB.

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
| TCVClo {body : Expr} {Γ_clo : Env Ty} {τa τr : Ty} {ρ_clo : Env Val}
  : (ENV ρ_clo ⊨ Γ_clo) ->
    (TC (extend Γ_clo τa) ⊢ body : τr) ->
    (TCV ⊢ v_clo τa body ρ_clo : (τa ~> τr))
with
tc_env : Env Val -> Env Ty -> Type :=
| TCENil : tc_env nil nil
| TCECons {v τ ρ Γ} :
    tc_env ρ Γ ->
    tc_val v τ ->
    tc_env (v :: ρ) (τ :: Γ)
where "'TCV' ⊢ v : τ" := (tc_val v τ)
and "'ENV' ρ ⊨ Γ" := (tc_env ρ Γ).

Scheme tc_val_env_rect := Induction for tc_val Sort Type
with
tc_env_val_rect := Induction for tc_env Sort Type.

Lemma lookup_tc_env {Γ ρ} (Hρ : ENV ρ ⊨ Γ) {x τ v} :
  lookup Γ x = Some τ ->
  lookup ρ x = Some v ->
  (TCV ⊢ v : τ).
Proof.
  intros.
  revert x H H0.
  induction Hρ; intros. {
    destruct x; inversion H.
  } {
    destruct x; simpl in *. {
      inversion H.
      inversion H0.
      subst.
      auto.
    } {
      eapply IHHρ; eauto.
    }
  }
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
  | e_lam τa body => Some (v_clo τa body ρ)
  | e_var x => lookup ρ x
  end.

Reserved Notation "'EVAL' ρ , σ ⊢ e ⇓ v , w" (at level 69, e at level 99, no associativity).
Inductive eval (ρ : Env Val) (σ : Entropy) : forall (e : Expr) (v : Val) (w : R+), Type :=
| EPure (ae : AExpr) (v : Val) :
    eval_a ρ ae = Some v ->
    (EVAL ρ, σ ⊢ e_pure ae ⇓ v, nnr_1)
| EApp {e0 e1 : Expr} {τa}
       {body : Expr} {ρ_clo : Env Val}
       {v1 v2 : Val}
       {w0 w1 w2 : R+}
  : (EVAL ρ, (π 0 σ) ⊢ e0 ⇓ v_clo τa body ρ_clo, w0) ->
    (EVAL ρ, (π 1 σ) ⊢ e1 ⇓ v1, w1) ->
    (EVAL (extend ρ_clo v1), (π 2 σ) ⊢ body ⇓ v2, w2) ->
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

(* There can be only one! *)

Lemma type_highlander :
  forall {e Γ τa τb}
         (tc_a : (TC Γ ⊢ e : τa))
         (tc_b : (TC Γ ⊢ e : τb)),
    τa = τb.
Proof.
  intro e.
  einduction e using Expr_AExpr_rect
  with (P0 := fun ae : AExpr =>
                forall Γ τa τb
                       (tc_a : (TC Γ ⊢ e_pure ae : τa))
                       (tc_b : (TC Γ ⊢ e_pure ae : τb)),
                  τa = τb);
intros;
try solve [eapply IHe0; eauto];
inversion tc_a;
inversion tc_b;
subst;
auto. {
    specialize (IHe0_1 _ _ _ H1 H6).
    inversion IHe0_1; auto.
  } {
    f_equal.
    eapply IHe0; eauto.
  } {
    rewrite H0 in H3.
    injection H3.
    auto.
  }
Qed.

Lemma tc_highlander :
  forall {e Γ τ} (tc_a tc_b : (TC Γ ⊢ e : τ)), tc_a = tc_b.
Proof.
  intro e.

  einduction e using Expr_AExpr_rect
  with (P0 := fun ae : AExpr =>
                forall Γ τ (tc_a tc_b : TC Γ ⊢ e_pure ae : τ),
                  tc_a = tc_b);
intros;
auto;
dependent destruction tc_a;
dependent destruction tc_b;
auto. {
    pose proof type_highlander tc_a1 tc_b1.
    inversion H.
    subst.
    rewrite (IHe0_1 _ _ tc_a1 tc_b1).
    rewrite (IHe0_2 _ _ tc_a2 tc_b2).
    auto.
  } {
    rewrite (IHe0 _ _ tc_a tc_b).
    auto.
  } {
    rewrite (IHe0_1 _ _ tc_a1 tc_b1).
    rewrite (IHe0_2 _ _ tc_a2 tc_b2).
    auto.
  } {
    rewrite (IHe0 _ _ tc_a tc_b).
    auto.
  } {
    f_equal.
    apply proof_irrelevance.
  }
Qed.

(* Fixpoint ty_env_highlander *)
(*   {Γa Γb : Env Ty} *)
(*   {ρ : Env Val} *)
(*   (HΓa : (ENV ρ ⊨ Γa)) *)
(*   (HΓb : (ENV ρ ⊨ Γb)) : *)
(*   Γa = Γb *)
(* with *)
(* vtype_highlander *)
(*   {v τa τb} *)
(*   (tc_a : (TCV ⊢ v : τa)) *)
(*   (tc_b : (TCV ⊢ v : τb)) : *)
(*   τa = τb. *)
(* Proof. { *)
(*     revert Γa Γb HΓa HΓb. *)
(*     induction ρ; intros; *)
(* dependent destruction HΓa; *)
(* dependent destruction HΓb; *)
(* subst. { *)
(*       auto. *)
(*     } { *)
(*       f_equal. { *)
(*         eapply vtype_highlander; eauto. *)
(*       } { *)
(*         apply IHρ; auto. *)
(*       } *)
(*     } *)
(*   } { *)
(*     intros. *)
(*     destruct tc_a; dependent destruction tc_b. { *)
(*       auto. *)
(*     } { *)
(*       f_equal. *)
(*       specialize (ty_env_highlander Γ_clo Γ_clo0 ρ_clo t t1). *)
(*       subst. *)
(*       eapply type_highlander; eauto. *)
(*     } *)
(*   } *)
(* Qed. *)

Lemma vtype_highlander :
  forall {v τa τb}
         (tc_a : (TCV ⊢ v : τa))
         (tc_b : (TCV ⊢ v : τb)),
    τa = τb.
Proof.
  intros.
  revert τb tc_b.
  einduction tc_a using tc_val_env_rect
  with (P0 := fun ρ Γ Hρ => forall Γb, (ENV ρ ⊨ Γb) -> Γ = Γb);
intros; auto. {
    inversion tc_b; subst.
    auto.
  } {
    inversion tc_b; subst.
    f_equal.
    specialize (IHt Γ_clo0 X).
    subst.
    eapply type_highlander; eauto.
  } {
    inversion X.
    auto.
  } {
    dependent destruction X.
    assert (ENV (v :: ρ) ⊨ (τ :: Γ)) by (constructor; auto).
    f_equal. {
      apply IHt0; auto.
    } {
      apply IHt; auto.
    }
  }
Qed.

Lemma ty_env_highlander
  {Γa Γb : Env Ty}
  {ρ : Env Val}
  (HΓa : (ENV ρ ⊨ Γa))
  (HΓb : (ENV ρ ⊨ Γb))
  : Γa = Γb.
Proof.
  revert Γa Γb HΓa HΓb.
  induction ρ; intros; inversion HΓa; inversion HΓb; subst. {
    auto.
  } {
    f_equal. {
      eapply vtype_highlander; eauto.
    } {
      apply IHρ; auto.
    }
  }
Qed.

Lemma tcv_highlander : forall {v τ} (a b : TCV ⊢ v : τ), a = b.
Proof.
  intros.
  revert b.

  einduction a using tc_val_env_rect
  with (P0 :=
          fun ρ Γa Hρa =>
            forall (Γb : Env Ty) (Hρb : ENV ρ ⊨ Γb),
              Γa = Γb /\ Hρa ~= Hρb);
intros. {
    dependent destruction b; auto.
  } {
    dependent destruction b.
    destruct (IHt _ t1).
    do 2 subst.
    f_equal.
    apply tc_highlander.
  } {
    dependent destruction Hρb; auto.
  } {
    assert (τ :: Γ = a). {
      assert (ENV (v :: ρ) ⊨ (τ :: Γ)) by (constructor; auto).
      exact (ty_env_highlander X Hρb).
    }
    split; auto.
    subst.
    enough (TCECons t t0 = Hρb); subst; auto.
    dependent destruction Hρb.
    destruct (IHt Γ Hρb).
    subst.
    f_equal.
    apply IHt0; auto.
  }
Qed.

Lemma tc_env_highlander {Γ ρ} (a b : ENV ρ ⊨ Γ) : a = b.
Proof.
  induction a; dependent destruction b; auto.
  rewrite (IHa b); auto.
  f_equal.
  apply tcv_highlander.
Qed.

Definition WT_Val τ := {v : Val & (TCV ⊢ v : τ) }.

Definition env_search {ρ Γ} (Hρ : ENV ρ ⊨ Γ) :
  forall x τ,
    lookup Γ x = Some τ ->
    {v : WT_Val τ | lookup ρ x = Some (projT1 v)}.
Proof.
  intros.
  revert ρ Γ H Hρ.
  induction x; intros. {
    destruct Γ; inversion H; subst.
    destruct ρ; inversion Hρ; subst.
    exists (existT _ v X0).
    auto.
  } {
    destruct Γ; inversion H; subst.
    destruct ρ; inversion Hρ; subst.
    simpl in *.
    eapply IHx; eauto.
  }
Defined.

Lemma WT_Val_eq {τ} {v v' : WT_Val τ} :
  projT1 v = projT1 v' -> v = v'.
Proof.
  intros.
  destruct v, v'.
  simpl in H.
  subst.
  f_equal.
  apply tcv_highlander.
Qed.

Lemma env_model_extend
      {ρ Γ} (Hρ : ENV ρ ⊨ Γ) {τ} (v : WT_Val τ)
  : ENV (extend ρ (projT1 v)) ⊨ (extend Γ τ).
Proof.
  destruct v.
  constructor; auto.
Qed.

Fixpoint decidable_tc Γ (e : Expr) {struct e} :
  ({τ : Ty & TC Γ ⊢ e : τ}) + (~exists τ, inhabited (TC Γ ⊢ e : τ))
with decidable_tc_pure Γ (ae : AExpr) :
  ({τ : Ty & TC Γ ⊢ e_pure ae : τ}) + (~exists τ, inhabited (TC Γ ⊢ e_pure ae : τ)).
Proof. {
    induction e. {
      destruct IHe1; [|right]. {
        destruct IHe2; [|right]. {
          destruct s as [τf Hf], s0 as [τa Ha].
          destruct τf; [right|]. {
            intro z.
            destruct z as [? []].
            inversion H; subst.
            pose proof (type_highlander H2 Hf).
            inversion H0.
          } {
            destruct (ty_eq_dec τf1 τa); [left | right]. {
              subst.
              repeat econstructor; eauto.
            } {
              intro z.
              destruct z as [? []].
              inversion H; subst.
              pose proof (type_highlander H2 Hf).
              inversion H0; subst.
              pose proof (type_highlander H4 Ha).
              contradiction.
            }
          }
        } {
          intro z.
          destruct z as [? []].
          inversion H; subst.
          apply n.
          repeat econstructor; eauto.
        }
      } {
        intro z.
        destruct z as [? []].
        inversion H; subst.
        apply n.
        repeat econstructor; eauto.
      }
    } {
      destruct IHe; [|right]. {
        destruct s as [[]]; [left | right]. {
          repeat econstructor; eauto.
        } {
          intro z.
          destruct z as [? []].
          inversion H; subst.
          pose proof (type_highlander t1 H1).
          inversion H0.
        }
      } {
        intro z.
        destruct z as [? []].
          inversion H; subst.
          apply n.
          repeat econstructor; eauto.
      }
    } {
      left.
      repeat econstructor; eauto.
    } {
      destruct IHe1 as [[[]]|]; [| right | right ]. {
        destruct IHe2 as [[[]]|]; [left | right | right ]. {
          repeat econstructor; eauto.
        } {
          intro z.
          destruct z as [? []].
          inversion H; subst.
          pose proof (type_highlander H4 t2).
          inversion H0.
        } {
          intro z.
          destruct z as [? []].
          inversion H; subst.
          apply n.
          repeat econstructor; eauto.
        }
      } {
        intro z.
        destruct z as [? []].
        inversion H; subst.
        pose proof (type_highlander H2 t1).
        inversion H0.
      } {
        intro z.
        destruct z as [? []].
        inversion H; subst.
        apply n.
        repeat econstructor; eauto.
      }
    } {
      apply decidable_tc_pure.
    }
  } {
    induction ae. {
      left.
        repeat econstructor; eauto.
    } {
      destruct (decidable_tc (extend Γ t) e); [left | right]. {
        destruct s.
        do 2 econstructor; eauto.
      } {
        intro z.
        destruct z.
        apply n.
        inversion H.
        inversion H0.
        subst.
        exists τr.
        repeat econstructor; eauto.
      }
    } {
      remember (lookup Γ v).
      destruct o; [left | right]. {
        exists t.
        constructor.
        auto.
      } {
        intro z.
        inversion z.
        inversion H.
        inversion H0.
        rewrite <- Heqo in H2.
        inversion H2.
      }
    }
  }
Qed.

Require Import Coq.Logic.Classical.

Lemma decidable_tc_env
      (decidable_tcv :
         forall v, ({τ : Ty & TCV ⊢ v : τ}) + (~exists τ, inhabited (TCV ⊢ v : τ)))
      (ρ : Env Val) :
  ({Γ : Env Ty & ENV ρ ⊨ Γ}) + (~exists Γ, inhabited (ENV ρ ⊨ Γ)).
Proof.
  induction ρ. {
    left.
    exists nil.
    constructor.
  } {
    destruct (decidable_tcv a); [|right]. {
      destruct IHρ; [|right]. {
        left.
        destruct s, s0.
        exists (x :: x0).
        constructor; auto.
      } {
        intro z.
        destruct z as [? []].
        inversion X; subst.
        apply n.
        repeat econstructor.
        eauto.
      }
    } {
      intro z.
      destruct z as [? []].
      inversion X; subst.
      apply n.
      repeat econstructor.
      eauto.
    }
  }
Qed.

Lemma decidable_tcv (v : Val) :
  ({τ : Ty & TCV ⊢ v : τ}) + (~exists τ, inhabited (TCV ⊢ v : τ)).
Proof.
  einduction v using Val_Val_Env_rect
  with (P0 := fun ρ =>
                (({Γ : Env Ty & ENV ρ ⊨ Γ}) +
                 (~exists Γ, inhabited (ENV ρ ⊨ Γ)))%type).
  {
    left.
    repeat econstructor; eauto.
  } {
    destruct IHv0; [| right]. {
      destruct s as [Γ Hρ].
      destruct (decidable_tc (extend Γ τ) e); [left | right]. {
        destruct s as [τr He].
        repeat econstructor; eauto.
      } {
        intro z.
        destruct z as [? []].
        inversion X; subst.
        pose proof (ty_env_highlander Hρ X0).
        subst.
        apply n.
        repeat econstructor; eauto.
      }
    } {
      intro z.
      destruct z as [? []].
      inversion X; subst.
      apply n.
      repeat econstructor; eauto.
    }
  } {
    left.
    repeat econstructor; eauto.
  } {
    destruct IHv0; [|right]. {
      destruct s as [τr Hv].
      destruct IHv1; [left | right]. {
        destruct s as [Γ ?].
        repeat econstructor; eauto.
      } {
        intro z.
        destruct z as [? []].
        inversion X; subst.
        apply n.
        repeat econstructor; eauto.
      }
    } {
      intro z.
      destruct z as [? []].
      inversion X; subst.
      apply n.
      repeat econstructor; eauto.
    }
  }
Qed.
