Require Import Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.JMeq.
Require Import Coq.Logic.FunctionalExtensionality.

Notation "a ⨉ b" := (prod a b) (at level 40, left associativity).

Parameter Var : Type.
Parameter Var_eq_dec : forall x y : Var, {x = y} + {x <> y}.

Inductive Ty :=
| B : Ty
| Arrow : Ty -> Ty -> Ty
.
Notation "x ~> y" := (Arrow x y) (at level 69, right associativity, y at level 70).

Inductive Expr :=
| e_bool : bool -> Expr
| e_var : Var -> Expr
| e_lam : Var -> Ty -> Expr -> Expr
| e_app : Expr -> Expr -> Expr
| e_if : Expr -> Expr -> Expr -> Expr
.

Notation "#t" := (e_bool true).
Notation "#f" := (e_bool false).
Notation "` x" := (e_var x) (at level 69).
Notation "'λ' x ; τ , e" := (e_lam x τ e) (at level 69, right associativity).
Notation "e0 @ e1" := (e_app e0 e1) (at level 68, left associativity).
Notation "'if_' e0 'then' e1 'else' e2" := (e_if e0 e1 e2) (at level 67, right associativity).

Definition Env (T : Type) := Var -> option T.
Definition empty_env {T : Type} : Env T := const None.
Notation "·" := empty_env.
Definition extend {T} (ρ : Env T) (x : Var) (v : T) : Env T :=
  fun y => if Var_eq_dec x y then Some v else ρ y.
Notation "ρ [ x → v ]" := (extend ρ x v) (at level 68, left associativity).
Definition map_env {A B : Type} : (A -> B) -> Env A -> Env B :=
  fun f ρ x =>
    match ρ x with
    | None => None
    | Some a => Some (f a)
    end.

Reserved Notation "'TC' Γ ⊢ e : τ" (at level 70, e at level 99, no associativity).
Inductive tc {Γ : Env Ty} : Expr -> Ty -> Prop :=
| TCBool (b : bool)
  : TC Γ ⊢ e_bool b : B
| TCVar (x : Var) (τ : Ty)
  : Γ x = Some τ ->
    TC Γ ⊢ `x : τ
| TCLam (x : Var) (τa τr : Ty) (body : Expr)
  : (TC Γ[x → τa] ⊢ body : τr) ->
    TC Γ ⊢ λ x ; τa , body : τa ~> τr
| TCApp (e0 e1 : Expr) (τa τr : Ty)
  : (TC Γ ⊢ e0 : τa ~> τr) ->
    (TC Γ ⊢ e1 : τa) ->
    TC Γ ⊢ e0 @ e1 : τr
| TCIf (e0 e1 e2 : Expr) (τ : Ty)
  : (TC Γ ⊢ e0 : B) ->
    (TC Γ ⊢ e1 : τ) ->
    (TC Γ ⊢ e2 : τ) ->
    (TC Γ ⊢ if_ e0 then e1 else e2 : τ)
where "'TC' Γ ⊢ e : τ" := (tc (Γ := Γ) e τ)
.

Inductive Val :=
| v_bool : bool -> Val
| v_clo : Var -> Expr -> Env (Val * Ty) -> Val.


Fixpoint val_models (τ : Ty) (v : Val) : Prop :=
  match τ, v with
  | B, v_bool _ => True
  | τa ~> τr, v_clo x e ρ => True (* Well, what should it be? *)
  | _, _ => False
  end.
Notation "'VAL' τ ⊨ v" := (val_models τ v) (at level 69, no associativity).

Reserved Notation "'EVAL' ρ ⊢ e ⇓ v" (at level 69, e at level 99, no associativity).
Inductive eval (ρ : Env (Val * Ty)) : Expr -> Val -> Prop :=
| EVar (x : Var) (v : Val) (τ : Ty)
  : ρ x = Some (v, τ) ->
    EVAL ρ ⊢ `x ⇓ v
| EConst (b : bool)
  : EVAL ρ ⊢ e_bool b ⇓ v_bool b
| ELam  (x : Var) (τ : Ty) (e : Expr)
  : EVAL ρ ⊢ λ x ; τ , e ⇓ v_clo x e ρ
| EApp (e0 e1 : Expr)
       (x : Var) (body : Expr) (ρ_clo : Env (Val * Ty))
       (τa : Ty)
       (v1 v2 : Val)
  : EVAL ρ ⊢ e0 ⇓ v_clo x body ρ_clo ->
    EVAL ρ ⊢ e1 ⇓ v1 ->
    EVAL ρ_clo[x → (v1, τa)] ⊢ body ⇓ v2 ->
    EVAL ρ ⊢ e0 @ e1 ⇓ v2
| EIfTrue (e0 e1 e2 : Expr) (v : Val)
  : (EVAL ρ ⊢ e0 ⇓ v_bool true) ->
    (EVAL ρ ⊢ e1 ⇓ v) ->
    EVAL ρ ⊢ if_ e0 then e1 else e2 ⇓ v
| EIfFalse (e0 e1 e2 : Expr) (v : Val)
  : (EVAL ρ ⊢ e0 ⇓ v_bool false) ->
    (EVAL ρ ⊢ e2 ⇓ v) ->
    EVAL ρ ⊢ if_ e0 then e1 else e2 ⇓ v
where "'EVAL' ρ ⊢ e ⇓ v" := (eval ρ e v)
.

Definition Config := Env (Val ⨉ Ty) ⨉ Expr.

Definition E_rel' (V_rel : Ty -> Val -> Prop) (τ : Ty) (c : Config) : Prop :=
  let (ρ, e) := c in
  exists v,
    (TC (map_env snd ρ) ⊢ e : τ) /\
    (EVAL ρ ⊢ e ⇓ v) /\
    V_rel τ v.

Fixpoint V_rel τ v : Prop :=
  match τ, v with
  | B, v_bool _ => True
  | τa ~> τr, v_clo x e ρ =>
    forall v',
      let ρ' := ρ[x → (v', τa)] in
      V_rel τa v'->
      (TC (map_env snd ρ') ⊢ e : τr) /\
      E_rel' V_rel τr (ρ', e)
  | _, _ => False
  end
.

Definition E_rel := E_rel' V_rel.

Lemma V_rel_models : forall {τ v}, V_rel τ v -> VAL τ ⊨ v.
Proof.
  intros.
  induction τ, v; simpl; auto.
Qed.

Definition env_dom_eq {A B} (envA : Env A) (envB : Env B) :=
  forall x, envA x = None <-> envB x = None.

Record env_models {Γ : Env Ty} {ρ : Env (Val * Ty)} : Type :=
  {
    env_dom_match : env_dom_eq Γ ρ;
    env_val_models : forall x τ,
        Γ x = Some τ ->
        {v | ρ x = Some (v, τ) /\ VAL τ ⊨ v}
  }.
Notation "'ENV' Γ ⊨ ρ" := (@env_models Γ ρ) (at level 69, no associativity).

Lemma env_models_replacable Γ ρ:
  ENV Γ ⊨ ρ-> map_env snd ρ = Γ.
Proof.
  intros.
  extensionality x.
  unfold map_env.
  remember (Γ x).
  induction o.
  -
    induction (env_val_models X x a); auto.
    rewrite (proj1 p); auto.
  -
    induction (env_dom_match X x).
    rewrite H; auto.
Qed.

Record G_rel {Γ : Env Ty} {ρ : Env (Val * Ty)} : Type :=
  {
    G_rel_modeling : ENV Γ ⊨ ρ;
    G_rel_V : forall x τ (pf1 : Γ x = Some τ),
        V_rel τ (proj1_sig (env_val_models G_rel_modeling x τ pf1));
  }.
Arguments G_rel _ _ : clear implicits.

Definition related_expr (Γ : Env Ty) (τ : Ty) (e : Expr) : Prop :=
  TC Γ ⊢ e : τ /\
             forall ρ,
               G_rel Γ ρ ->
               E_rel τ (ρ, e).
Notation "'EXP' Γ ⊢ e0 ≈ e1 : τ" :=
  (related_expr Γ e0 e1 τ)
    (at level 69, e0 at level 99, e1 at level 99, no associativity).

Lemma env_pair :
  forall {A B} (Γ : Env (A * B)) x b,
    (map_env snd Γ) x = Some b -> {a | Γ x = Some (a, b)}.
Proof.
  intros.
  unfold map_env in *.
  induction (Γ x).
  induction a.
  exists a.
  repeat apply f_equal.
  inversion H.
  auto.
  contradict H; discriminate.
Qed.

Ltac split3 := split; [|split].
Ltac decompose_common b :=
  let H := fresh "H" in
  pose proof b as H;
  hnf in H;
  decompose [ex sum and sig sigT G_rel @env_models] H;
  clear H.
(* absurdly common typo I'm sick of correcting *)
Ltac inductino a := induction a.


Lemma rel_implies_models τ v : V_rel τ v -> VAL τ ⊨ v.
Proof.
  intros.
  induction τ, v; simpl; eauto.
Qed.

Lemma compat_bool Γ b :
  related_expr Γ B (e_bool b).
Proof.
  split.
  apply TCBool.
  exists (v_bool b).
  split3; simpl; auto.
  apply TCBool.
  apply EConst.
Qed.

Lemma compat_var Γ x τ :
  Γ x = Some τ ->
  related_expr Γ τ (`x).
Proof.
  intros; split.
  apply TCVar; tauto.
  intros ρ grel.
  induction grel.
  pose proof (G_rel_V0 x τ H).
  induction (env_val_models _ x τ) as [v]; auto.
  simpl in *.
  exists v.
  split3; auto. {
    rewrite (env_models_replacable Γ); auto.
    apply TCVar; auto.
  } {
    apply EVar with (τ := τ); auto.
    apply (proj1 p).
  }
Qed.

Lemma compat_lam Γ x body τa τr :
  (* TC Γ[x → τa] ⊢ body : τr -> *)
  related_expr (Γ[x → τa]) τr body ->
  related_expr Γ (τa ~> τr) (λ x ; τa , body).
Proof.
  intros IH.
  split. {
    apply TCLam.
    apply IH.
  } {
    intros ρ grel.
    induction grel.
    exists (v_clo x body ρ).
    split3. {
      rewrite (env_models_replacable Γ); auto.
      apply TCLam.
      apply IH.
    } {
      apply ELam.
    } {
      simpl.
      intros.
      induction (proj2 IH (ρ[x → (v', τa)])). {
        split; eauto.
        apply H0.
      }
      enough (env'_model : ENV Γ[x → τa] ⊨ ρ[x → (v', τa)]). {
        split with (G_rel_modeling := env'_model).
        intros.
        unfold extend in *.
        generalize (env_val_models env'_model x0 τ pf1).
        induction s; simpl.
        induction Var_eq_dec. {
          induction p.
          inversion H0.
          rewrite <- H3, <- H4.
          auto.
        } {
          pose proof (G_rel_V0 x0 τ pf1).
          induction G_rel_modeling0; simpl in *.
          induction env_val_models0; simpl in *.
          cutrewrite (x1 = x2); auto.
          inversion p.
          inversion p0.
          rewrite H1 in *.
          inversion H3.
          auto.
        }
      } {
        repeat split;
unfold extend;
try inductino Var_eq_dec;
try discriminate;
try apply G_rel_modeling0.

        intros.
        induction Var_eq_dec. {
          exists v'.
          inversion H0.
          split; auto.
          induction G_rel_modeling0; simpl in *.
          apply V_rel_models.
          rewrite <- H2; auto.
        } {
          apply G_rel_modeling0; auto.
        }
      }
    }
  }
Qed.

Lemma compat_app Γ ef ea τa τr :
  related_expr Γ (τa ~> τr) ef ->
  related_expr Γ τa ea ->
  related_expr Γ τr (ef @ ea).
Proof.
  intros IHf IHa.
  split. {
    apply TCApp with (τa0 := τa).
    apply IHf.
    apply IHa.
  } {
    intros ρ grel.
    induction IHf as [tcd_f Hf], IHa as [tcd_a Ha].
    induction (Hf ρ grel).
    decompose_common H; clear H.
    induction (Ha ρ grel).
    decompose_common H; clear H.
    induction x; [contradict H3; tauto|].
    rename e0 into ρ_clo.
    induction (H4 x0); auto.
    rename v into x.
    rename x0 into v.
    induction H0 as [vr].
    exists vr.
    split3. {
      apply TCApp with (τa0 := τa); auto.
    } {
      apply (EApp ρ _ _ x e ρ_clo τa v); eauto.
      apply H0.
    } {
      apply H0.
    }
  }
Qed.

Lemma compat_if Γ e0 e1 e2 τ :
  related_expr Γ B e0 ->
  related_expr Γ τ e1 ->
  related_expr Γ τ e2 ->
  related_expr Γ τ (if_ e0 then e1 else e2).
Proof.
  intros IH0 IH1 IH2.
  assert (TC Γ ⊢ if_ e0 then e1 else e2 : τ). {
    apply TCIf; [apply IH0 | apply IH1 | apply IH2].
  }
  split; auto.
  intros ρ grel.
  decompose_common (proj2 IH0 ρ grel).
  rename x into v0.
  simpl in *.
  induction v0; intuition.
  induction b;
[decompose_common (proj2 IH1 ρ grel) | decompose_common (proj2 IH2 ρ grel)];
exists x;
split3;
try rewrite (env_models_replacable Γ);
induction grel;
auto.
  apply EIfTrue; tauto.
  apply EIfFalse; tauto.
Qed.


Lemma well_typed_is_related
      {τ Γ e} (tc_deriv : TC Γ ⊢ e : τ) : related_expr Γ τ e.
  induction tc_deriv.
  - apply compat_bool.
  - apply compat_var; auto.
  - apply compat_lam; auto.
  - apply compat_app with (τa := τa); auto.
  - apply compat_if; auto.
Qed.

Lemma related_is_terminating τ e :
  related_expr · τ e ->
  exists v, EVAL · ⊢ e ⇓ v.
Proof.
  intros.
  induction H.
  induction (H0 ·).
  exists x.
  apply H1.
  assert (ENV · ⊨ ·). {
    repeat split; auto.
    discriminate.
  }
  exists X.
  discriminate.
Qed.

Theorem STLC_terminates :
  forall e τ,
    (TC · ⊢ e : τ) ->
    exists v, EVAL · ⊢ e ⇓ v.
Proof.
  intros.
  apply (related_is_terminating τ).
  apply well_typed_is_related.
  assumption.
Qed.

Print Assumptions STLC_terminates.
