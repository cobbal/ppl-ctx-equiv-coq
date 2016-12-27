Require Import utils.
Require Import syntax.
Require Import relations.
Require Import RelationClasses.

(* Symmetry *)

Lemma A_rel_symmetric' {τ} :
  Symmetric (V_rel τ) ->
  Symmetric (A_rel τ).
Proof.
  repeat intro.
  apply eq_sym.
  apply H0, H, Hv.
Qed.

Lemma E_rel_symmetric' {τ} :
  Symmetric (V_rel τ) ->
  Symmetric (E_rel τ).
Proof.
  repeat intro.
  apply eq_sym.
  apply H0.
  apply A_rel_symmetric'; auto.
Qed.

Instance V_rel_symmetric {τ} : Symmetric (V_rel τ).
Proof.
  repeat intro.
  induction τ; destruct_val x; destruct_val y. {
    apply eq_sym.
    exact H.
  } {
    destruct H.

    constructor.
    intros.

    apply E_rel_symmetric'; auto.
    apply H.
    auto.
  }
Qed.

Instance E_rel_symmetric {τ} : Symmetric (E_rel τ)
  := E_rel_symmetric' V_rel_symmetric.
Instance A_rel_symmetric {τ} : Symmetric (A_rel τ)
  := A_rel_symmetric' V_rel_symmetric.

Instance G_rel_symmetric {Γ} : Symmetric (G_rel Γ).
Proof.
  repeat intro.
  induction Γ; d_destruct (x, y). {
    constructor.
  } {
    d_destruct H.
    constructor. {
      apply V_rel_symmetric.
      auto.
    } {
      apply IHΓ.
      auto.
    }
  }
Qed.

Instance rel_expr_symmetric {Γ τ} : Symmetric (expr_rel Γ τ).
Proof.
  intros e0 e1 He ? ? ?.
  symmetry.
  apply He.
  symmetry.
  auto.
Qed.

(* Transitivity *)

Instance A_rel_transitive' {τ} :
  Transitive (V_rel τ) ->
  Transitive (A_rel τ).
Proof.
  intros ? x y z Hxy Hyz.
  intros v0 v1 Hv.
  transitivity (y v0); auto.
  apply Hxy.
  transitivity v1; [| symmetry]; exact Hv.
Qed.

Instance E_rel_transitive' {τ} :
  Transitive (V_rel τ) ->
  Transitive (E_rel τ).
Proof.
  intros ? x y z Hxy Hyz.
  repeat intro.

  transitivity (μ y A0); auto.
  apply Hxy.
  transitivity A1; [| symmetry]; exact HA.
Qed.

Instance V_rel_transitive {τ} :
  Transitive (V_rel τ).
Proof.
  repeat intro.
  induction τ;
    destruct_val x;
    destruct_val y;
    destruct_val z.
  {
    transitivity (v_real r0); auto.
  } {
    constructor.
    intros.

    remember (v_lam body).
    destruct H.
    remember (v_lam body3).
    remember (v_lam body1).
    destruct H0.
    d_destruct (Heqv, Heqv0, Heqv1).
    clear body0.

    eapply (E_rel_transitive' IHτ2 _ (proj1_sig (ty_subst1 body3 va0))); [| apply H0; auto].
    apply H.

    eapply IHτ1; eauto.
    symmetry.
    auto.
  }
Qed.

Instance E_rel_transitive {τ} : Transitive (E_rel τ)
  := E_rel_transitive' V_rel_transitive.
Instance A_rel_transitive {τ} : Transitive (A_rel τ)
  := A_rel_transitive' V_rel_transitive.

Instance G_rel_transitive {Γ} : Transitive (G_rel Γ).
Proof.
  repeat intro.
  induction Γ; d_destruct (x, y, z). {
    constructor.
  } {
    d_destruct H.
    d_destruct H1.
    constructor. {
      etransitivity; eauto.
    } {
      eapply IHΓ; eauto.
    }
  }
Qed.

Instance rel_expr_transitive {Γ τ} : Transitive (expr_rel Γ τ).
Proof.
  intros x y z Hxy Hyz ? ? ?.

  transitivity (proj1_sig (close ρ0 y)). {
    apply Hxy.
    transitivity ρ1; [| symmetry]; exact H.
  } {
    apply Hyz.
    exact H.
  }
Qed.


(* Reflexivity *)

(* reflexivity depends on the fundamental property. *)

Lemma A_rel_subidentity {τ} {A0 A1 : Event (val τ)}
  : A_rel τ A0 A1 -> A0 = A1.
Proof.
  intros.
  extensionality v.
  apply H.
  apply fundamental_property_of_values.
Qed.

Instance E_rel_reflexive {τ} : Reflexive (E_rel τ).
Proof.
  intro e.
  pose proof (fundamental_property _ _ e _ _ G_rel_nil).
  elim_sig_exprs.
  elim_erase_eqs.
  auto.
Qed.

Instance V_rel_reflexive {τ} : Reflexive (V_rel τ).
Proof.
  intros v.
  apply fundamental_property_of_values.
Qed.

Instance G_rel_reflexive {Γ} : Reflexive (G_rel Γ).
Proof.
  repeat intro.
  induction Γ; d_destruct x. {
    constructor.
  } {
    constructor; auto.
    apply V_rel_reflexive.
  }
Qed.

Instance rel_expr_reflexive {Γ τ} : Reflexive (expr_rel Γ τ)
  := fundamental_property _ _.

Lemma same_substitution_suffices {Γ τ} (e0 e1 : expr Γ τ) :
  (forall (ρ : wt_env Γ),
      E_rel τ (proj1_sig (close ρ e0)) (proj1_sig (close ρ e1))) ->
  (EXP Γ ⊢ e0 ≈ e1 : τ).
Proof.
  intros ? ρ0 ρ1 Hρ.

  transitivity (proj1_sig (close ρ0 e1)). {
    apply H.
  } {
    apply fundamental_property; auto.
  }
Qed.

Lemma relate_exprs {Γ τ} (e0 e1 : expr Γ τ) :
  (forall ρ A, μ (proj1_sig (close ρ e0)) A = μ (proj1_sig (close ρ e1)) A) ->
  (EXP Γ ⊢ e0 ≈ e1 : τ).
Proof.
  intros.

  apply same_substitution_suffices; auto.

  repeat intro.

  rewrite (A_rel_subidentity HA).
  apply H.
Qed.