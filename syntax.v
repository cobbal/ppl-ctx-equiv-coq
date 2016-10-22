Require Import Reals.
Require Import List.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import nnr.
Require Export Entropy.
Require Import utils.
Require Import List.

Require Export Autosubst.Autosubst.

Local Open Scope R.

Definition Var := var.
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
| e_real : R -> Expr
| e_lam : Ty -> {bind Expr} -> Expr
| e_var : var -> Expr
.

Definition is_pure (e : Expr) : Prop :=
  match e with
  | e_real _ | e_lam _ _ | e_var _ => True
  | _ => False
  end.

Instance Ids_Expr : Ids Expr. derive. Defined.
Instance Rename_Expr : Rename Expr. derive. Defined.
Instance Subst_Expr : Subst Expr. derive. Defined.
Instance SubstLemmas_Expr : SubstLemmas Expr. derive. Defined.

Definition Env (T : Type) := list T.
Definition empty_env {T : Type} : Env T := nil.
Definition extend {T} (ρ : Env T) (v : T) : Env T :=
  v :: ρ.
Fixpoint lookup {T} (ρ : Env T) x : option T :=
  match ρ with
  | nil => None
  | v :: ρ' =>
    match x with
    | O => Some v
    | S x' => lookup ρ' x'
    end
  end.
Notation "·" := empty_env.

Reserved Notation "'TC' Γ ⊢ e : τ" (at level 70, e at level 99, no associativity).
Inductive tc {Γ : Env Ty} : Expr -> Ty -> Type :=
| TCReal (r : R)
  : (TC Γ ⊢ e_real r : ℝ)
| TCVar {x : Var} {τ : Ty}
  : lookup Γ x = Some τ ->
    (TC Γ ⊢ e_var x : τ)
| TCLam {τa τr : Ty} {body : Expr}
  : (TC (extend Γ τa) ⊢ body : τr) ->
    (TC Γ ⊢ e_lam τa body : τa ~> τr)
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

Definition is_val (e : Expr) : Prop :=
  match e with
  | e_real _ | e_lam _ _ => True
  | _ => False
  end.

Record Val :=
  mk_Val {
      Val_e :> Expr;
      Val_v : is_val Val_e;
    }.

Lemma Val_rect
      (P : Val -> Type)
      (case_real : (forall r, P (mk_Val (e_real r) I)))
      (case_lam : (forall τa body, P (mk_Val (e_lam τa body) I))) :
  forall v, P v.
Proof.
  intros.
  destruct v.
  destruct Val_e0;
try contradiction Val_v0;
replace Val_v0 with I by apply proof_irrelevance;
auto.
Defined.

Ltac absurd_Val :=
  match goal with
  | [ H : context[ (Val_e ?v) ] |- _ ] =>
    contradict (rew <- H in Val_v v) +
    contradict (rew H in Val_v v)
  end.

Reserved Notation "'EVAL' σ ⊢ e ⇓ v , w" (at level 69, e at level 99, no associativity).
Inductive eval (σ : Entropy) : forall (e : Expr) (v : Val) (w : R+), Type :=
| EPure {v : Val} :
    (EVAL σ ⊢ v ⇓ v, nnr_1)
| EApp {e0 e1 : Expr} {τa}
       {body : Expr}
       {v1 v2 : Val}
       {w0 w1 w2 : R+}
  : (EVAL (π 0 σ) ⊢ e0 ⇓ mk_Val (e_lam τa body) I, w0) ->
    (EVAL (π 1 σ) ⊢ e1 ⇓ v1, w1) ->
    (EVAL (π 2 σ) ⊢ body.[(v1 : Expr)/] ⇓ v2, w2) ->
    (EVAL σ ⊢ e_app e0 e1 ⇓ v2, w0 [*] w1 [*] w2)
| EFactor {e : Expr} {r : R} {w : R+} (rpos : 0 <= r)
  : (EVAL σ ⊢ e ⇓ mk_Val (e_real r) I, w) ->
    (EVAL σ ⊢ e_factor e ⇓ mk_Val (e_real r) I, mknnr r rpos [*] w)
| ESample
  : (EVAL σ ⊢ e_sample ⇓ mk_Val (e_real (proj1_sig (σ 0%nat))) I, nnr_1)
| EPlus {e0 e1 : Expr} {r0 r1 : R} {is_v0 is_v1} {w0 w1 : R+}
  : (EVAL (π 0 σ) ⊢ e0 ⇓ mk_Val (e_real r0) is_v0, w0) ->
    (EVAL (π 1 σ) ⊢ e1 ⇓ mk_Val (e_real r1) is_v1, w1) ->
    (EVAL σ ⊢ e_plus e0 e1 ⇓ mk_Val (e_real (r0 + r1)) I, w0 [*] w1)
where "'EVAL' σ ⊢ e ⇓ v , w" := (eval σ e v w)
.

Definition EPure' (σ : Entropy) (e : Expr) (v : Val) :
  e = v ->
  (EVAL σ ⊢ e ⇓ v, nnr_1).
Proof.
  intros.
  rewrite H.
  constructor.
Qed.

Lemma expr_type_unique :
  forall {e Γ τa τb}
         (tc_a : (TC Γ ⊢ e : τa))
         (tc_b : (TC Γ ⊢ e : τb)),
    τa = τb.
Proof.
  intro e.
  induction e;
intros;
try solve [eapply IHe0; eauto];
inversion tc_a;
inversion tc_b;
subst;
auto. {
    specialize (IHe1 _ _ _ X1 X).
    inversion IHe1; auto.
  } {
    f_equal.
    eapply IHe; eauto.
  } {
    rewrite H0 in H3.
    inversion H3.
    auto.
  }
Qed.

Lemma tc_unique :
  forall {e Γ τ} (tc_a tc_b : (TC Γ ⊢ e : τ)),
    tc_a = tc_b.
Proof.
  intro e.

  induction e;
intros;
auto;
dependent destruction tc_a;
dependent destruction tc_b;
auto. {
    pose proof expr_type_unique tc_a1 tc_b1.
    inversion H.
    subst.
    rewrite (IHe1 _ _ tc_a1 tc_b1).
    rewrite (IHe2 _ _ tc_a2 tc_b2).
    auto.
  } {
    rewrite (IHe _ _ tc_a tc_b).
    auto.
  } {
    rewrite (IHe1 _ _ tc_a1 tc_b1).
    rewrite (IHe2 _ _ tc_a2 tc_b2).
    auto.
  } {
    rewrite (IHe _ _ tc_a tc_b).
    auto.
  } {
    f_equal.
    apply proof_irrelevance.
  }
Qed.

Record WT_Val τ :=
  mk_WT_Val {
      WT_Val_v :> Val;
      WT_Val_tc : (TC · ⊢ WT_Val_v : τ);
    }.
Arguments mk_WT_Val {_} _ _.
Arguments WT_Val_v {_} _.
Arguments WT_Val_tc {_} _.

Definition v_real r : WT_Val ℝ :=
  mk_WT_Val (mk_Val (e_real r) I) (TCReal r).

Definition v_lam τa body : Val :=
  mk_Val (e_lam τa body) I.

Lemma WT_Val_arrow_rect {τa τr}
      (P : WT_Val (τa ~> τr) -> Type)
      (case_lam :
         (forall body (Hbody : (TC (extend · τa) ⊢ body : τr)),
             P (mk_WT_Val
                  (mk_Val (e_lam τa body) I)
                  (TCLam Hbody)))) :
  forall v, P v.
Proof.
  intros.

  destruct v as [v Hv].
  destruct v using Val_rect. {
    inversion Hv.
  } {
    inversion Hv; subst.
    replace Hv with (TCLam X) by apply tc_unique.
    apply case_lam.
  }
Defined.

Lemma WT_Val_real_rect
      (P : WT_Val ℝ -> Type)
      (case_real :
         (forall r,
             P (mk_WT_Val
                  (mk_Val (e_real r) I)
                  (TCReal r)))) :
  forall v, P v.
Proof.
  intros.

  destruct v as [v Hv].
  destruct v using Val_rect. {
    replace Hv with (@TCReal · r) by apply tc_unique.
    apply case_real.
  } {
    inversion Hv.
  }
Defined.

Lemma WT_Val_rect {τ}
      (P : WT_Val τ -> Type)
      (case_real :
         (forall r (τeq : ℝ = τ),
             P (mk_WT_Val
                  (mk_Val (e_real r) I)
                  (rew τeq in TCReal r))))
      (case_lam :
         (forall τa τr
                 (τeq : (τa ~> τr) = τ)
                 body
                 (Hbody : (TC (extend · τa) ⊢ body : τr)),
             P (mk_WT_Val
                  (mk_Val (e_lam τa body) I)
                  (rew τeq in TCLam Hbody)))) :
  forall v, P v.
Proof.
  intros.
  destruct τ. {
    apply WT_Val_real_rect.
    intros.
    exact (case_real r eq_refl).
  } {
    apply WT_Val_arrow_rect.
    intros.
    exact (case_lam _ _ eq_refl body Hbody).
  }
Defined.

Ltac destruct_WT_Val wt_v :=
  match (type of wt_v) with
  | WT_Val ℝ =>
    destruct wt_v using WT_Val_real_rect
  | WT_Val (?τa ~> ?τr) =>
    destruct wt_v using WT_Val_arrow_rect
  end.

Inductive TCEnv : Env Val -> Env Ty -> Type :=
| TCENil : TCEnv · ·
| TCECons {v : Val} {τ ρ' Γ'} : (TC · ⊢ v : τ) -> TCEnv ρ' Γ' -> TCEnv (v :: ρ') (τ :: Γ')
.

Record WT_Env Γ :=
  mk_WT_Env {
      WT_Env_ρ :> Env Val;
      WT_Env_tc : TCEnv WT_Env_ρ Γ;
    }.
Arguments mk_WT_Env {_ _} _.
Arguments WT_Env_ρ {_} _.
Arguments WT_Env_tc {_} _.

Definition WT_nil : WT_Env · := mk_WT_Env TCENil.

Lemma tc_env_unique {Γ ρ} (Hρ0 Hρ1 : TCEnv Γ ρ) : Hρ0 = Hρ1.
Proof.
  dependent induction Hρ0
  ; dependent destruction Hρ1
  ; auto.

  f_equal; auto.
  apply tc_unique.
Qed.

Lemma wt_nil_unique : forall ρ, ρ = WT_nil.
Proof.
  intros [ρ Hρ].
  unfold WT_nil.
  f_equal.
  dependent destruction Hρ.
  reflexivity.
Qed.

(* borrowed from a comment in autosubst, hope it's right *)
Fixpoint sapp {X : Type} (l : list X) (sigma : nat -> X) : nat -> X :=
  match l with nil => sigma | cons s l' => s .: sapp l' sigma end.
Infix ".++" := sapp (at level 55, right associativity) : subst_scope.
Arguments sapp {_} !l sigma / _.

Definition downgrade_env : Env Val -> Env Expr := map (fun x : Val => x : Expr).

Definition subst_of_WT_Env {Γ} (ρ : WT_Env Γ) : nat -> Expr :=
  sapp (downgrade_env ρ) ids.

Lemma subst_of_WT_Env_lookup {Γ x v} {ρ : WT_Env Γ} :
  (lookup ρ x = Some v) ->
  subst_of_WT_Env ρ x = v.
Proof.
  intros.
  unfold subst_of_WT_Env.
  destruct ρ as [ρ].
  simpl in *.
  clear WT_Env_tc0.
  revert ρ H.
  induction x; intros. {
    destruct ρ; try discriminate.
    inversion H.
    autosubst.
  } {
    destruct ρ; try discriminate.
    apply IHx.
    auto.
  }
Qed.

Lemma extend_TCE {Γ ρ τ} (Hρ : TCEnv ρ Γ) (v : WT_Val τ)
  : TCEnv (extend ρ v) (extend Γ τ).
Proof.
  constructor; auto.
  apply v.
Qed.

Definition extend_WT_Env {Γ τ} (ρ : WT_Env Γ) (v : WT_Val τ) : WT_Env (extend Γ τ) :=
  mk_WT_Env (extend_TCE (WT_Env_tc ρ) v).


Lemma Val_eq {v v' : Val} :
  @eq Expr v v' -> @eq Val v v'.
Proof.
  intros.
  destruct v, v'.
  simpl in *.
  subst.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma WT_Val_eq {τ} {v v' : WT_Val τ} :
  @eq Expr v v' -> @eq (WT_Val τ) v v'.
Proof.
  intros.
  destruct v as [[]], v' as [[]].
  simpl in *.
  subst.
  replace Val_v1 with Val_v0 by apply proof_irrelevance.
  f_equal.
  apply tc_unique.
Qed.

Definition env_search {ρ Γ} (Hρ : TCEnv ρ Γ) {x τ} :
  lookup Γ x = Some τ ->
  {v : WT_Val τ | lookup ρ x = Some (WT_Val_v v)}.
Proof.
  intros.
  revert ρ Γ H Hρ.
  induction x; intros. {
    destruct Γ; inversion H; subst.
    destruct ρ; inversion Hρ; subst.
    exists (mk_WT_Val _ X).
    auto.
  } {
    destruct Γ; inversion H; subst.
    destruct ρ; inversion Hρ; subst.
    simpl in *.
    eapply IHx; eauto.
  }
Qed.

Lemma decidable_tc Γ (e : Expr) :
  ({τ : Ty & TC Γ ⊢ e : τ}) + (~exists τ, inhabited (TC Γ ⊢ e : τ)).
Proof.
  revert Γ.
  induction e; intros. {
    destruct (IHe1 Γ); [|right]. {
      destruct (IHe2 Γ); [|right]. {
        destruct s as [τf Hf], s0 as [τa Ha].
        destruct τf; [right|]. {
          intro z.
          destruct z as [? []].
          inversion X; subst.
          pose proof (expr_type_unique X0 Hf).
          inversion H.
        } {
          destruct (ty_eq_dec τf1 τa); [left | right]. {
            subst.
            repeat econstructor; eauto.
          } {
            intro z.
            destruct z as [? []].
            inversion X; subst.
            pose proof (expr_type_unique X0 Hf).
            inversion H; subst.
            pose proof (expr_type_unique X1 Ha).
            contradiction.
          }
        }
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
  } {
    destruct (IHe Γ); [|right]. {
      destruct s as [[]]; [left | right]. {
        repeat econstructor; eauto.
      } {
        intro z.
        destruct z as [? []].
        inversion X; subst.
        pose proof (expr_type_unique t1 X0).
        inversion H.
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
    destruct (IHe1 Γ) as [[[]]|]; [| right | right ]. {
      destruct (IHe2 Γ) as [[[]]|]; [left | right | right ]. {
        repeat econstructor; eauto.
      } {
        intro z.
        destruct z as [? []].
        inversion X; subst.
        pose proof (expr_type_unique X1 t2).
        inversion H.
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
      pose proof (expr_type_unique X0 t1).
      inversion H.
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
    destruct (IHe (extend Γ t)); [left | right]. {
      destruct s.
      do 2 econstructor; eauto.
    } {
      intro z.
      destruct z.
      apply n.
      inversion H.
      inversion X.
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
      inversion X; subst.
      rewrite <- Heqo in H1.
      discriminate H1.
    }
  }
Qed.


Lemma general_weakening Γ1 {Γ0 e τ} :
  (TC Γ0 ⊢ e : τ) ->
  (TC Γ0 ++ Γ1 ⊢ e : τ).
Proof.
  intros He.
  induction He; try solve [econstructor; eauto]. {
    constructor.
    revert x e.
    induction Γ; intros. {
      discriminate.
    } {
      destruct x; auto.
      simpl in *.
      apply IHΓ.
      auto.
    }
  }
Qed.

Lemma weaken {Γ e τ} :
  (TC · ⊢ e : τ) ->
  (TC Γ ⊢ e : τ).
Proof.
  intros.
  replace Γ with (· ++ Γ) by auto.
  apply general_weakening.
  auto.
Qed.

Lemma ty_ren {Γ e τ} :
  (TC Γ ⊢ e : τ) ->
  forall Δ ξ,
    lookup Γ = ξ >>> lookup Δ ->
    (TC Δ ⊢ e.[ren ξ] : τ).
Proof.
  induction 1; try solve [econstructor; eauto]. {
    intros.
    rewrite H in e.
    simpl in e.
    constructor.
    auto.
  } {
    intros.
    constructor.
    set (ξ' x := match x with | O => O | S x => S (ξ x) end).
    assert (ren ξ' = up (ren ξ)). {
      subst ξ'.
      extensionality x.
      destruct x; auto.
    }
    rewrite <- H0.
    apply IHX.
    subst ξ'.
    extensionality x.
    simpl.
    rewrite H.
    simpl.
    destruct x; auto.
  }
Qed.

Lemma ty_subst {Γ e τ} :
  (TC Γ ⊢ e : τ) -> forall σ Δ,
    (forall x τ',
        lookup Γ x = Some τ' ->
        (TC Δ ⊢ σ x : τ')) ->
  (TC Δ ⊢ e.[σ] : τ).
Proof.
  induction 1; try solve [econstructor; eauto]; intros. {
    apply X.
    auto.
  } {
    constructor.
    apply IHX.
    intros [|]. {
      intros.
      simpl in *.
      constructor.
      auto.
    } {
      intros.
      simpl in H.
      specialize (X0 _ _ H).

      pose proof (ty_ren X0).
      specialize (X1 (extend Δ τa) S eq_refl).
      autosubst.
    }
  }
Qed.

Lemma ty_subst1 {τa e τr} (v : WT_Val τa) :
  (TC extend · τa ⊢ e : τr) ->
  (TC · ⊢ e.[v : Expr/] : τr).
Proof.
  intros He.
  apply (ty_subst He).
  intros.
  destruct x. {
    simpl in *.
    inversion H; subst.
    apply v.
  } {
    simpl in *.
    discriminate H.
  }
Qed.

Lemma body_subst {Γ τa τr body} (ρ : WT_Env Γ) :
  (TC extend Γ τa ⊢ body : τr) ->
  (TC extend · τa ⊢ body.[up (subst_of_WT_Env ρ)] : τr).
Proof.
  intros tc_body.
  apply (ty_subst tc_body).
  intros.

  destruct x. {
    simpl in *.
    unfold up.
    simpl.
    constructor; auto.
  } {
    unfold up.
    simpl in *.
    rewrite rename_subst.
    destruct (env_search (WT_Env_tc ρ) H).
    pose proof subst_of_WT_Env_lookup e.
    rewrite H0.

    apply (ty_ren (WT_Val_tc x0)).
    extensionality x'.
    simpl.
    auto.
  }
Qed.
