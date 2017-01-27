Require Import Coq.Classes.RelationClasses.

Require Import utils.
Require Import syntax.
Require Import relations.
Require Import integration.

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
  induction τ. {
    apply eq_sym.
    exact H.
  } {
    destruct H.

    constructor.
    intros.

    apply E_rel_symmetric'; auto.
    apply H.
    apply IHτ1.
    exact H0.
  }
Qed.

Instance E_rel_symmetric {τ} : Symmetric (E_rel τ)
  := E_rel_symmetric' V_rel_symmetric.
Instance A_rel_symmetric {τ} : Symmetric (A_rel τ)
  := A_rel_symmetric' V_rel_symmetric.

Instance G_rel_symmetric {Γ} : Symmetric (G_rel Γ).
Proof.
  repeat intro.
  induction Γ; dep_destruct (x, y). {
    constructor.
  } {
    dep_destruct H.
    constructor; auto.
    symmetry.
    assumption.
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
  induction τ.
  {
    transitivity y; assumption.
  } {
    destruct H.
    remember (v_lam body1).
    destruct H0.
    dep_destruct Heqv.
    rename body0 into x_body, body1 into y_body, body3 into z_body.

    constructor.
    intros.

    eapply (E_rel_transitive' IHτ2 _); [| apply H0; eauto].
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
  induction Γ; dep_destruct (x, y, z). {
    constructor.
  } {
    dep_destruct H.
    dep_destruct H1.
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

Instance E_rel_reflexive {τ} : Reflexive (E_rel τ).
Proof.
  intro e.
  pose proof (fundamental_property e _ _ G_rel_nil).
  elim_sig_exprs.
  elim_erase_eqs.
  auto.
Qed.

Instance V_rel_reflexive {τ} : Reflexive (V_rel τ).
Proof.
  intros v.

  destruct v using wt_val_rect; subst; simpl in *. {
    reflexivity.
  } {
    constructor.
    repeat intro.

    pose proof fundamental_property body as fp.
    specialize (fp _ _ (G_rel_cons H G_rel_nil)).

    elim_sig_exprs.
    elim_erase_eqs.

    apply fp; auto.
  }
Qed.

Lemma A_rel_subidentity {τ} {A0 A1 : Event (val τ)}
  : A_rel τ A0 A1 -> A0 = A1.
Proof.
  intros.
  extensionality v.
  apply H.
  reflexivity.
Qed.

Instance G_rel_reflexive {Γ} : Reflexive (G_rel Γ).
Proof.
  repeat intro.
  induction Γ; dep_destruct x. {
    constructor.
  } {
    constructor; auto.
    reflexivity.
  }
Qed.

Instance rel_expr_reflexive {Γ τ} : Reflexive (expr_rel Γ τ)
  := fundamental_property.

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