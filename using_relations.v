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

Definition ex_left e1 e2 := (λ ℝ, (`O) +! inc_free_vars e1) @ e2.
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

    pose proof big_preservation TCENil He1 (π 0 σ) ex3.
    inversion X1; subst.

    pose proof big_preservation TCENil He2 (π 1 σ) ex4.
    inversion X2; subst.

    specialize (u3 (_, _) X).
    specialize (u4 (_, _) X0).
    inversion u3.
    inversion u4.
    subst.

    repeat f_equal.
    apply tcv_highlander.
  } {
    simpl.
    unfold ev, ew.
    decide_eval TCENil, He1 as [v3 w3 ex3 u3].
    decide_eval TCENil, He2 as [v4 w4 ex4 u4].
    contradict not_ex.

    pose proof big_preservation TCENil He1 (π 0 σ) ex3.
    inversion X; subst.

    pose proof big_preservation TCENil He2 (π 1 σ) ex4.
    inversion X0; subst.

    eexists (_, _).
    constructor; eauto.
  }
Qed.

Lemma length_of_models {Γ ρ} : (ENV ρ ⊨ Γ) -> length ρ = length Γ.
Proof.
  intros.
  induction X; auto.
  simpl.
  rewrite IHX.
  auto.
Qed.

Lemma insert_models {Γ ρ v τ} n Hlenρ HlenΓ :
  (ENV ρ ⊨ Γ) ->
  (TCV ⊢ v : τ) ->
  (ENV insert_at ρ n v Hlenρ ⊨ insert_at Γ n τ HlenΓ).
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

Lemma eval_ignored_variable {Γ ρ vi τi σ e τ v0 v1 w} :
  (TC Γ ⊢ e : τ) ->
  (TCV ⊢ vi : τi) ->
  (ENV ρ ⊨ Γ) ->
  (EVAL ρ, σ ⊢ e ⇓ v1, w) ->
  (EVAL extend ρ vi, σ ⊢ inc_free_vars e ⇓ v0, w) ->
  (VREL v0, v1 ∈ V[τ]).
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
    refine (big_preservation (insert_models _ _ _ _ _) (tc_inc' τi H0 He) σ X); auto.
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
    pose proof big_preservation Hρ H2 _ E0_1.
    pose proof big_preservation Hρ H4 _ E0_2.
    inversion X2; subst.
    pose proof env_model_extend X4 (existT _ v1 X3).
    simpl in *.
    eapply IHE0_3; eauto.

    inversion


  }

  dependent induction X; intros. {
    destruct e; try discriminate x.
    destruct ae, a; try discriminate x; simpl in *; try solve [destruct lt_dec; inversion x]. {
      inversion x; subst.
      inversion e0; subst.
      inversion E0; subst.
      inversion H1; subst.
      inversion He; subst.
      constructor.
    } {
      inversion x; subst.
      inversion e0; subst.
      inversion E0; subst.
      inversion H1; subst.
      inversion He; subst.
      clear x e0 E0 H1 He.
      simpl.
      split; auto.

      assert (n <= length Γ). {
        rewrite <- (length_of_models Hρ).
        auto.
      }
      exists (insert_at Γ n τi H0).
      exists (insert_models _ _ _ Hρ Hvi).

      pose proof tc_inc' (n := S n) τi (ext_len _ H0) H4.
      rewrite <- extend_of_insert in H1.
      exists H1.

      exists Γ.
      exists Hρ.
      exists H4.

      intros ? ? Hva.
      intros ? ? HA.

      unfold μ.
      f_equal.
      extensionality σ0.

      unfold eval_in, ev, ew.
      decide_eval _, _ as [v0 w0 ex0 u0]. {
        decide_eval _, _ as [v1 w1 ex1 u1]. {
          clear u0 u1.
          (* specialize (u0 (v1, w1)). *)
          (* simpl in u0. *)
          simpl.

          unfold Indicator, widen_event.
          simpl.
          do 2 f_equal. {
            apply HA.
            simpl.
            admit.
          } {

          }















          assert (EVAL extend (insert_at ρ n vi H) (projT1 va0), σ0 ⊢ inc_vars (S n) e1 ⇓ v1, w1). {
            admit.
          }
          injection (u0 X); intros; subst.
          unfold Indicator, widen_event.
          do 2 f_equal.
          apply HA.
          simpl.
          apply fundamental_property_of_values.

          apply (big_preservation (env_model_extend Hρ _) H4 _ ex1).
        } {
          contradict not_ex.
          exists (v0, w0).
        }
      }


    }
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

    apply eval_ignored_variable_l in X3.

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
