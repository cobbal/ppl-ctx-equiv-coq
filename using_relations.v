Require Import Basics.
Require Import Reals.
Require Import List.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import nnr.
Require Import syntax.
Require Import utils.
Require Import Coq.Classes.Morphisms.
Require Import relations.
Require Import micromega.Lia.
Import EqNotations.

(* Local Open Scope R. *)
Opaque π.

Fixpoint appears_free_in (x : Var) (e : Expr) : bool :=
  match e with
  | e_app e0 e1 => orb (appears_free_in x e0) (appears_free_in x e1)
  | e_factor e0 => appears_free_in x e0
  | e_sample => false
  | e_plus e0 e1 => orb (appears_free_in x e0) (appears_free_in x e1)
  | e_pure (e_real _) => false
  | e_pure (e_lam τa body) => appears_free_in (S x) body
  | e_pure (e_var x') => if Var_eq_dec x x' then true else false
  end.

(* Inductive Ctx := *)
(* | c_hole : Ctx *)
(* | c_app_l : Ctx -> Expr -> Ctx *)
(* | c_app_r : Expr -> Ctx -> Ctx *)
(* | c_factor : Ctx -> Ctx *)
(* | c_plus_l : Ctx -> Expr -> Ctx *)
(* | c_plus_r : Expr -> Ctx -> Ctx *)
(* | c_lam : Ty -> Ctx -> Ctx *)
(* . *)

(* Fixpoint plug (C : Ctx) (e : Expr) : Expr := *)
(*   match C with *)
(*   | c_hole => e *)
(*   | c_app_l c0 e1 => e_app (plug c0 e) e1 *)
(*   | c_app_r e0 c1 => e_app e0 (plug c1 e) *)
(*   | c_factor c0 => e_factor (plug c0 e) *)
(*   | c_plus_l c0 e1 => e_plus (plug c0 e) e1 *)
(*   | c_plus_r e0 c1 => e_plus e0 (plug c1 e) *)
(*   | c_lam τa cbody => e_pure (e_lam τa (plug cbody e)) *)
(*   end. *)

Fixpoint discard_binding (x : Var) (e : Expr) : Expr :=
  match e with
  | e_app e0 e1 => e_app (discard_binding x e0) (discard_binding x e1)
  | e_factor e0 => e_factor (discard_binding x e0)
  | e_sample => e_sample
  | e_plus e0 e1 => e_plus (discard_binding x e0) (discard_binding x e1)
  | e_pure (e_real r) => e_pure (e_real r)
  | e_pure (e_lam τa body) => e_pure (e_lam τa (discard_binding (S x) body))
  | e_pure (e_var x') =>
    if lt_dec x' x
    then e_pure (e_var x')
    else e_pure (e_var (pred x'))
  end.

Definition inc_vars : Var -> Expr -> Expr :=
  fix i x e :=
    match e with
    | e_app e0 e1 => e_app (i x e0) (i x e1)
    | e_factor e0 => e_factor (i x e0)
    | e_sample => e_sample
    | e_plus e0 e1 => e_plus (i x e0) (i x e1)
    | e_pure (e_real r) => e_pure (e_real r)
    | e_pure (e_lam τa body) => e_pure (e_lam τa (i (S x) body))
    | e_pure (e_var x') =>
      if lt_dec x' x
      then e_pure (e_var x')
      else e_pure (e_var (S x'))
    end.
Definition inc_free_vars := inc_vars O.

Notation "x ~> y" := (Arrow x y) (at level 69, right associativity, y at level 70).
Notation "` x" := (e_pure (e_var x)) (at level 72).
Notation "'λ' τ , e" := (e_pure (e_lam τ e)) (at level 69, right associativity).
Notation "e0 @ e1" := (e_app e0 e1) (at level 68, left associativity).
Notation "e0 +! e1" := (e_plus e0 e1) (at level 68, left associativity).

Definition ex_left e1 e2 := (λ ℝ, (`O) +! inc_free_vars e2) @ e1.
Definition ex_right e1 e2 := e1 +! e2.

Program Fixpoint insert_at {X} (l : list X) (n : nat) (x : X) (Hn : n <= length l) {struct n} : list X :=
  match n with
  | O => x :: l
  | S n' =>
    match l with
    | (l0 :: ls) => l0 :: insert_at ls n' x _
    | nil => False_rect _ _
    end
  end.
Next Obligation.
  simpl in *.
  lia.
Qed.
Next Obligation.
  contradict Hn.
  simpl.
  lia.
Qed.

Lemma tc_inc' {Γ τr e n} τ0 (Hn : n <= length Γ) :
  (TC Γ ⊢ e : τr) ->
  (TC insert_at Γ n τ0 Hn ⊢ inc_vars n e : τr).
Proof.
  intros.
  revert n Hn.
  induction H; simpl; intros; try solve [econstructor; simpl; eauto]. {
    destruct lt_dec. {
      constructor.
      rewrite <- e.
      clear e τ.

      revert n Hn l.
      revert Γ.
      induction x; intros. {
        destruct Γ; simpl in Hn. {
          exfalso.
          lia.
        } {
          destruct n; try lia.
          auto.
        }
      } {
        destruct Γ. {
          exfalso.
          simpl in Hn.
          lia.
        } {
          destruct n; try lia.
          simpl in *.
          assert (n <= length Γ) by lia.
          assert (x < n) by lia.
          specialize (IHx Γ n H H0).
          rewrite <- IHx.
          repeat f_equal.
          apply le_unique.
        }
      }
    } {
      constructor.
      apply not_lt in n0.
      revert x n0 Γ e Hn.
      induction n; intros; auto.

      destruct x, Γ; simpl in *; try solve [discriminate | lia].
      assert (x >= n) by lia.
      assert (n <= length Γ) by lia.
      rewrite <- IHn with (Hn := H0) (x := x); auto.
      repeat f_equal.
      apply le_unique.
    }
  } {
    constructor.
    assert (S n <= S (length Γ)) by lia.
    specialize (IHtc _ H0).
    enough (insert_at (extend Γ τa) (S n) τ0 H0 =
            extend (insert_at Γ n τ0 Hn) τa). {
      rewrite <- H1.
      auto.
    } {
      unfold extend.
      simpl.
      repeat f_equal.
      apply le_unique.
    }
  }
Qed.

Lemma tc_inc {Γ τr e} τ0 :
  (TC Γ ⊢ e : τr) ->
  (TC extend Γ τ0 ⊢ inc_free_vars e : τr).
Proof.
  assert (0 <= length Γ) by (simpl; lia).
  replace (extend Γ τ0) with (insert_at Γ 0 τ0 H) by trivial.
  apply tc_inc'.
Qed.

(* Require Import ExtensionalityFacts. *)
(* Lemma shuffle_entropy (π π_inv : nat -> nat) (f : Entropy -> R+) : *)
(*   is_inverse π π_inv -> *)
(*   Integration f μEntropy = *)
(*   Integration (fun σ => f (σ ∘ π)) μEntropy. *)
(* Proof. *)
(*   intros. *)
(*   rewrite riemann_def_of_lebesgue_integration. *)
(*   symmetry. *)
(*   rewrite riemann_def_of_lebesgue_integration. *)
(*   symmetry. *)
(*   f_equal. *)
(*   extensionality t. *)
(*   fold Entropy. *)
(* Admitted. *)


Lemma right_tc {e1 e2} :
  (TC Datatypes.nil ⊢ e1 : ℝ) ->
  (TC Datatypes.nil ⊢ e2 : ℝ) ->
  (TC nil ⊢ ex_right e1 e2 : ℝ).
Proof.
  constructor; auto.
Qed.

Lemma left_tc {e1 e2} :
  (TC Datatypes.nil ⊢ e1 : ℝ) ->
  (TC Datatypes.nil ⊢ e2 : ℝ) ->
  (TC nil ⊢ ex_left e1 e2 : ℝ).
Proof.
  repeat econstructor; auto.
  apply tc_inc; auto.
Qed.

Lemma break_right {e1 e2}
    (He1 : (TC nil ⊢ e1 : ℝ))
    (He2 : (TC nil ⊢ e2 : ℝ))
    σ A :
  eval_in TCENil (right_tc He1 He2) A σ =
  option0 (plus_in A <$> ev TCENil He1 (π 0 σ) <*> ev TCENil He2 (π 1 σ))
          [*] ew TCENil He1 (π 0 σ)
          [*] ew TCENil He2 (π 1 σ).
Proof.
  unfold eval_in.
  unfold ev at 1, ew at 1.
  decide_eval TCENil, _ as [v0 w0 ex0 u0]. {
    inversion ex0; subst.
    unfold ev, ew.
    decide_eval TCENil, He1 as [v3 w3 ex3 u3].
    decide_eval TCENil, He2 as [v4 w4 ex4 u4].
    rewrite <- nnr_mult_assoc.

    unfold plus_in.
    simpl.

    pose proof big_preservation TCENil He1 ex3.
    inversion X1; subst.

    pose proof big_preservation TCENil He2 ex4.
    inversion X2; subst.

    specialize (u3 (_, _) X).
    specialize (u4 (_, _) X0).
    inversion u3.
    inversion u4.
    subst.

    repeat f_equal.
    apply tc_val_unique.
  } {
    simpl.
    unfold ev, ew.
    decide_eval TCENil, He1 as [v3 w3 ex3 u3].
    decide_eval TCENil, He2 as [v4 w4 ex4 u4].
    contradict not_ex.

    pose proof big_preservation TCENil He1 ex3.
    inversion X; subst.

    pose proof big_preservation TCENil He2 ex4.
    inversion X0; subst.

    eexists (_, _).
    constructor; eauto.
  }
Qed.

Lemma length_of_models {Γ ρ} : (TCEnv ⊢ ρ : Γ) -> length ρ = length Γ.
Proof.
  intros.
  induction X; auto.
  simpl.
  rewrite IHX.
  auto.
Qed.

Lemma insert_models {Γ ρ v τ} n Hlenρ HlenΓ :
  (TCEnv ⊢ ρ : Γ) ->
  (TCV ⊢ v : τ) ->
  (TCEnv ⊢ insert_at ρ n v Hlenρ : insert_at Γ n τ HlenΓ).
Proof.
  revert Γ ρ Hlenρ HlenΓ.
  induction n; intros ? ? ? ? Hρ Hv. {
    simpl.
    constructor; auto.
  } {
    dependent destruction Hρ. {
      contradict Hlenρ.
      simpl.
      lia.
    } {
      simpl.
      constructor; auto.
    }
  }
Qed.


Lemma ext_len {X n} {Γ : Env X} τ :
  n <= length Γ ->
  S n <= length (extend Γ τ).
Proof.
  simpl; lia.
Qed.

Lemma extend_of_insert {X} (Γ : Env X) n τSn τ0 Hn :
  extend (insert_at Γ n τSn Hn) τ0 =
  insert_at (extend Γ τ0) (S n) τSn (ext_len _ Hn).
Proof.
  simpl.
  unfold extend.
  repeat f_equal.
  apply le_unique.
Qed.

Lemma lookup_before_insert {X} {ρ : Env X} {n x} (H : n <= length ρ) vi :
  x < n ->
  lookup (insert_at ρ n vi H) x = lookup ρ x.
Proof.
  intros.
  revert ρ n H H0.
  induction x. {
    intros.
    destruct ρ. {
      exfalso.
      simpl in *.
      lia.
    } {
      destruct n; try lia.
      auto.
    }
  } {
    intros.
    destruct ρ. {
      exfalso.
      simpl in *.
      lia.
    } {
      simpl.
      destruct n; try lia.
      apply IHx.
      lia.
    }
  }
Qed.

Check eval_rect.


(* Expr_rect *)
(*      : forall P : Expr -> Type, *)
(*        (forall e : Expr, P e -> forall e0 : Expr, P e0 -> P (e @ e0)) -> *)
(*        (forall e : Expr, P e -> P (e_factor e)) -> *)
(*        P e_sample -> *)
(*        (forall e : Expr, P e -> forall e0 : Expr, P e0 -> P (e +! e0)) -> *)
(*        (forall a : AExpr, P (e_pure a)) -> forall e : Expr, P e *)

(* Val_Val_Env_rect *)
(* : forall (P : Val -> Type) (P0 : Env Val -> Type), *)
(*   (forall r : R, P (v_real r)) -> *)
(*   (forall (τ : Ty) (e : Expr) (ρ : Env Val), P0 ρ -> P (v_clo τ e ρ)) -> *)
(*   P0 Datatypes.nil -> *)
(*   (forall (v : Val) (ρ' : Env Val), P v -> P0 ρ' -> P0 (v :: ρ')) -> forall v : Val, P v *)

(* eval_rect *)
(*      : forall *)
(*          P : forall (ρ : Env Val) (σ : Entropy) (e : Expr) (v : Val) (w : R+), *)
(*              EVAL ρ, σ ⊢ e ⇓ v, w -> Type, *)
(*        (forall (ρ : Env Val) (σ : Entropy) (ae : AExpr) (v : Val) (e : eval_a ρ ae = Some v), *)
(*         P ρ σ (e_pure ae) v nnr_1 (EPure ρ σ ae v e)) -> *)
(*        (forall (ρ : Env Val) (σ : Entropy) (e0 e1 : Expr) (τa : Ty) (body : Expr)  *)
(*           (ρ_clo : Env Val) (v1 v2 : Val) (w0 w1 w2 : R+) *)
(*           (e : EVAL ρ, π 0 σ ⊢ e0 ⇓ v_clo τa body ρ_clo, w0), *)
(*         P ρ (π 0 σ) e0 (v_clo τa body ρ_clo) w0 e -> *)
(*         forall e2 : EVAL ρ, π 1 σ ⊢ e1 ⇓ v1, w1, *)
(*         P ρ (π 1 σ) e1 v1 w1 e2 -> *)
(*         forall e3 : EVAL extend ρ_clo v1, π 2 σ ⊢ body ⇓ v2, w2, *)
(*         P (extend ρ_clo v1) (π 2 σ) body v2 w2 e3 -> *)
(*         P ρ σ (e0 @ e1) v2 (w0 [*] w1 [*] w2) (EApp ρ σ e e2 e3)) -> *)
(*        (forall (ρ : Env Val) (σ : Entropy) (e : Expr) (r : R) (w : R+) (rpos : (0 <= r)%R) *)
(*           (e0 : EVAL ρ, σ ⊢ e ⇓ v_real r, w), *)
(*         P ρ σ e (v_real r) w e0 -> *)
(*         P ρ σ (e_factor e) (v_real r) ({| _r := r; nnr_pos := rpos |} [*] w) (EFactor ρ σ rpos e0)) -> *)
(*        (forall (ρ : Env Val) (σ : Entropy), *)
(*         P ρ σ e_sample (v_real (proj1_sig (σ 0))) nnr_1 (ESample ρ σ)) -> *)
(*        (forall (ρ : Env Val) (σ : Entropy) (e0 e1 : Expr) (r0 r1 : R) (w0 w1 : R+) *)
(*           (e : EVAL ρ, π 0 σ ⊢ e0 ⇓ v_real r0, w0), *)
(*         P ρ (π 0 σ) e0 (v_real r0) w0 e -> *)
(*         forall e2 : EVAL ρ, π 1 σ ⊢ e1 ⇓ v_real r1, w1, *)
(*         P ρ (π 1 σ) e1 (v_real r1) w1 e2 -> *)
(*         P ρ σ (e0 +! e1) (v_real (r0 + r1)) (w0 [*] w1) (EPlus ρ σ e e2)) -> *)
(*        forall (ρ : Env Val) (σ : Entropy) (e : Expr) (v : Val) (w : R+) (e0 : EVAL ρ, σ ⊢ e ⇓ v, w), *)
(*        P ρ σ e v w e0 *)


(* Lemma eval_super_rect *)
(*       (PE : forall {ρ σ e v w}, *)
(*           forall {Γ τ}, *)
(*             (TCEnv ⊢ ρ : Γ) -> *)
(*             (TC Γ ⊢ e : τ) -> *)
(*             (EVAL ρ, σ ⊢ e ⇓ v, w) -> *)
(*           Type) *)
(*       (Pv : Val -> Type) *)

(*       (case_real : forall Γ ρ σ r (Hρ : (TCEnv ⊢ ρ : Γ)), *)
(*           PE Hρ (TCReal r) (EPure ρ σ (e_real r) (v_real r) eq_refl)) *)
(*       (case_lam : forall Γ ρ σ τa τr body *)
(*                          (Hρ : (TCEnv ⊢ ρ : Γ)) *)
(*                          (Hbody : (TC (extend Γ τa) ⊢ body : τr)), *)
(*           (forall (va : WT_Val τa) vr σ w *)
(*                   (Ebody : EVAL extend ρ (va : Val), σ ⊢ body ⇓ vr, w), *)
(*               PE (tc_env_extend Hρ va) Hbody Ebody) -> *)
(*           PE Hρ (TCLam Hbody) (EPure ρ σ (e_lam τa body) (v_clo τa body ρ) eq_refl)) *)
(*       (case_var : forall Γ ρ σ x v τ *)
(*                          (Hρ : (TCEnv ⊢ ρ : Γ)) *)
(*                          (Γx : lookup Γ x = Some τ) *)
(*                          (ρx : lookup ρ x = Some v), *)
(*           PE Hρ (TCVar Γx) (EPure ρ σ (e_var x) v ρx)) *)

(*       (case_app : *)
(*          forall Γ ρ σ e0 e1 τa τr body Γ_clo ρ_clo v1 v2 w0 w1 w2 *)
(*                 (Hρ : (TCEnv ⊢ ρ : Γ)) *)
(*                 (Hρ_clo : (TCEnv ⊢ ρ_clo : Γ_clo)) *)
(*                 (Hbody : TC extend Γ_clo τa ⊢ body : τr) *)
(*                 (He0 : (TC Γ ⊢ e0 : τa ~> τr)) *)
(*                 (He1 : (TC Γ ⊢ e1 : τa)) *)
(*                 (E0 : (EVAL ρ, π 0 σ ⊢ e0 ⇓ (v_clo τa body ρ_clo), w0)) *)
(*                 (E1 : (EVAL ρ, π 1 σ ⊢ e1 ⇓ v1, w1)) *)
(*                 (E2 : (EVAL extend ρ_clo v1, π 2 σ ⊢ body ⇓ v2, w2)), *)
(*            PE Hρ He0 E0 -> *)
(*            PE Hρ He1 E1 -> *)
(*            PE (tc_env_extend Hρ_clo (mk_WT_Val (big_preservation Hρ He1 E1))) Hbody E2 -> *)
(*            PE Hρ (TCApp He0 He1) (EApp ρ σ E0 E1 E2)) *)
(*       (case_factor : *)
(*          forall Γ ρ σ e r w rpos *)
(*                 (Hρ : (TCEnv ⊢ ρ : Γ)) *)
(*                 (He : (TC Γ ⊢ e : ℝ)) *)
(*                 (E0 : EVAL ρ, σ ⊢ e ⇓ v_real r, w), *)
(*            PE Hρ He E0 -> *)
(*            PE Hρ (TCFactor He) (EFactor ρ σ rpos E0)) *)
(*       (case_sample : *)
(*          forall Γ ρ σ *)
(*                 (Hρ : (TCEnv ⊢ ρ : Γ)), *)
(*            PE Hρ TCSample (ESample ρ σ)) *)
(*       (case_plus : *)
(*          forall Γ ρ σ e0 e1 r0 r1 w0 w1 *)
(*                 (Hρ : (TCEnv ⊢ ρ : Γ)) *)
(*                 (He0 : (TC Γ ⊢ e0 : ℝ)) *)
(*                 (He1 : (TC Γ ⊢ e1 : ℝ)) *)
(*                 (E0 : (EVAL ρ, π 0 σ ⊢ e0 ⇓ v_real r0, w0)) *)
(*                 (E1 : (EVAL ρ, π 1 σ ⊢ e1 ⇓ v_real r1, w1)), *)
(*          PE Hρ He0 E0 -> *)
(*          PE Hρ He1 E1 -> *)
(*          PE Hρ (TCPlus He0 He1) (EPlus ρ σ E0 E1)) *)

(*   : forall Γ ρ σ e v w τ *)
(*            (Hρ : (TCEnv ⊢ ρ : Γ)) *)
(*            (He : (TC Γ ⊢ e : τ)) *)
(*            (E : EVAL ρ, σ ⊢ e ⇓ v, w), *)
(*     PE Hρ He E. *)
(* Proof. *)
(*   intros. *)
(*   induction E; auto. { *)
(*     induction ae; auto. { *)
(*       inversion e; subst. *)
(*       inversion He; subst. *)

(*       assert (e = eq_refl) by apply proof_irrelevance. *)
(*       assert (He = TCReal r) by apply tc_unique. *)
(*       subst. *)

(*       apply case_real. *)
(*     } { *)
(*       inversion e; subst. *)
(*       inversion He; subst. *)

(*       assert (e = eq_refl) by apply proof_irrelevance. *)
(*       assert (He = TCLam H2) by apply tc_unique. *)
(*       subst. *)

(*       apply case_lam. *)

(*       intros. *)
(*     } *)
(*   } *)
(* Qed. *)





Lemma lookup_after_insert {X} {ρ : Env X} {n x} (H : n <= length ρ) vi :
  x >= n ->
  lookup (insert_at ρ n vi H) (S x) = lookup ρ x.
Proof.
  intros.
  revert ρ x H H0.
  induction n, ρ; intros. {
    destruct x; auto.
  } {
    destruct x0; simpl; auto.
  } {
    contradict H.
    simpl.
    lia.
  } {
    destruct x0; try lia.
    simpl.
    apply IHn.
    lia.
  }
Qed.

Lemma eval_ignored_variable_l {Γ ρ vi τi σ e τ vr w n} :
  forall (Hn : n <= length ρ),
    (TCEnv ⊢ ρ : Γ) ->
    (TC Γ ⊢ e : τ) ->
    (TCV ⊢ vi : τi) ->
    (EVAL insert_at ρ n vi Hn, σ ⊢ inc_vars n e ⇓ vr, w) ->
    {v : Val & EVAL ρ, σ ⊢ e ⇓ v, w & V_rel τ v vr}.
Proof.
  intros.
  revert Γ τ X H X0.
  dependent induction X1; intros. {
    destruct e; try discriminate x.
    destruct a. {
      destruct ae; inversion x.
      simpl in *.
      inversion e0; subst.
      inversion H; subst.
      eexists (v_real r); constructor; auto.
    } {

    }

  }

Qed.

Lemma eval_ignored_variable_l {Γ ρ vi τi σ e τ v0 v1 w} :
  (TC Γ ⊢ e : τ) ->
  (TCV ⊢ vi : τi) ->
  (TCEnv ⊢ ρ : Γ) ->
  (EVAL ρ, σ ⊢ e ⇓ v1, w) ->
  (EVAL extend ρ vi, σ ⊢ inc_free_vars e ⇓ v0, w) ->
  (V_rel τ v0 v1).
Proof.
  intros He Hvi Hρ E0.
  unfold inc_free_vars.
  assert (0 <= length ρ) by (destruct ρ; simpl; lia).
  replace (extend ρ vi) with (insert_at ρ 0 vi H) by trivial.
  revert H.
  generalize 0.
  intros.

  assert (TCV ⊢ v1 : τ) by (eapply big_preservation; eauto).
  assert (TCV ⊢ v0 : τ). {
    assert (n <= length Γ) by exact (rew length_of_models Hρ in H).
    refine (big_preservation (insert_models _ _ _ _ _) (tc_inc' τi H0 He) X); auto.
  }


  revert v0 X1 Γ He Hvi Hρ X.

  induction E0; intros. {
    destruct ae. {
      simpl in e.
      inversion e; subst.
      inversion He; subst.
      inversion X; subst.
      simpl in H1.
      inversion H1.
      subst.
      reflexivity.
    } {
      simpl in e.
      inversion e; subst.
      inversion He; subst.
      inversion X; subst.
      simpl in H1.
      inversion H1.
      subst.
      clear e He X H1.
      simpl.
      split; auto.
      admit.
    } {
      rename v1 into x.
      simpl in X.
      destruct lt_dec. {
        inversion X; subst.
        clear X.
        simpl in *.

        replace v0 with v; try apply fundamental_property_of_values; auto.

        pose proof lookup_before_insert H vi l.
        rewrite H1 in H0.
        rewrite e in H0.
        inversion H0.
        auto.
      } {
        inversion X; subst.
        clear X.
        simpl in *.

        replace v0 with v; try apply fundamental_property_of_values; auto.

        apply not_lt in n0.
        pose proof lookup_after_insert H vi n0.
        rewrite H1 in H0.
        rewrite e in H0.
        inversion H0.
        auto.
      }
    }
  } {
    inversion He; subst.
    pose proof big_preservation Hρ H2 E0_1.
    pose proof big_preservation Hρ H4 E0_2.
    inversion X2; subst.
    pose proof tc_env_extend X4 (mk_WT_Val X3).
    simpl in *.
    eapply IHE0_3; eauto.

    admit.
  }
Admitted.

Lemma eval_ignored_variable_r {Γ τ σ e v w} :
  (EVAL Γ, σ ⊢ e ⇓ v, w) ->
  (EVAL extend Γ τ, σ ⊢ inc_free_vars e ⇓ v, w).
Proof.
  intros.
  unfold inc_free_vars in *.
  (* really need a better IH here *)
  dependent induction X.
Admitted.

Lemma break_left {e1 e2}
      (He1 : (TC nil ⊢ e1 : ℝ))
      (He2 : (TC nil ⊢ e2 : ℝ))
      σ A :
  let σe1 := (π 1 (π 2 σ)) in
  let σe2 := (π 1 σ) in
  eval_in TCENil (left_tc He1 He2) A σ =
  option0 (plus_in A <$> ev TCENil He1 σe1 <*> ev TCENil He2 σe2)
          [*] ew TCENil He1 σe1
          [*] ew TCENil He2 σe2.
Proof.
  intros.
  unfold eval_in.
  unfold ev at 1, ew at 1.
  decide_eval TCENil, _ as [v0 w0 ex0 u0]. {
    inversion ex0; subst.
    inversion X; subst.
    simpl in *.
    inversion H0; subst.
    inversion X1; subst.
    inversion X2; subst.
    inversion H1; subst.
    clear H0 H1 X X1 X2.

    (* assert (inc_free_vars e1 = e1). { *)
    (* } *)

    pose proof eval_ignored_variable_l He1 (TCVReal r1) TCENil X3.

    unfold ev, ew.
    decide_eval TCENil, He1 as [v3 w3 ex3 u3].
    decide_eval TCENil, He2 as [v4 w4 ex4 u4].

    unfold plus_in.
    simpl.

    pose proof big_preservation TCENil He1 σe1 ex3.
    inversion X; subst.

    pose proof big_preservation TCENil He2 σe2 ex4.
    inversion X1; subst.

    injection (u3 (_, _) X3).
    injection (u4 (_, _) X0).
    intros.
    subst.

    rewrite nnr_mult_assoc.
    f_equal; try solve [nnr].
    f_equal.
    rewrite (Rplus_comm r1 r0).
    f_equal.
    apply tcv_highlander.
  } {
    simpl.
    unfold ev, ew.
    decide_eval TCENil, He1 as [v3 w3 ex3 u3].
    decide_eval TCENil, He2 as [v4 w4 ex4 u4].
    contradict not_ex.

    pose proof big_preservation TCENil He1 _ ex3.
    inversion X; subst.

    pose proof big_preservation TCENil He2 _ ex4.
    inversion X0; subst.

    eexists (v_real (r0 + r), nnr_1 [*] w4 [*] (nnr_1 [*] w3)).
    repeat econstructor; eauto.
    apply eval_ignored_variable_r.
    auto.
  }
Qed.

Lemma simpleish e1 e2 :
  (TC nil ⊢ e1 : ℝ) ->
  (TC nil ⊢ e2 : ℝ) ->
  (EXP nil ⊢ ex_left e1 e2 ≈ ex_right e1 e2 : ℝ).
Proof.
  intros He1 He2.

  refine (mk_related_exprs (left_tc He1 He2) (right_tc He1 He2) _).
  simpl.
  intros.

  destruct Hρ.
  inversion G_rel_modeling0.
  inversion G_rel_modeling1.
  subst.
  simpl.
  clear G_rel_V.

  unfold μ.

  apply (lemma_3 (fun σ0 σ1 => μEntropy σ0 = μEntropy σ1)); auto.
  intros W.
  unfold preimage.
  dependent destruction G_rel_modeling0.
  dependent destruction G_rel_modeling1.
  setoid_rewrite break_right.
  setoid_rewrite break_left.



Qed.
