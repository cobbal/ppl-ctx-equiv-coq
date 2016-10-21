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
  destruct H0.
  exists He1 He0.
  intros.
  apply eq_sym.
  apply He.
  apply A_rel_symmetric'; auto.
Qed.

Instance V_rel_symmetric {τ} : Symmetric (V_rel τ).
Proof.
  induction τ; repeat intro. {
    destruct x using Val_rect; try contradiction H.
    destruct y using Val_rect; try contradiction H.
    apply eq_sym.
    exact H.
  } {
    destruct x using Val_rect; try contradiction H.
    destruct y using Val_rect; try contradiction H.
    destruct H as [[? ?] [? [? ?]]].
    subst.
    split; auto.
    eexists; eauto.
    eexists; eauto.
    intros.
    apply E_rel_symmetric'; auto.
    apply H.
    apply IHτ1.
    apply H0.
  }
Qed.

Instance E_rel_symmetric {τ} : Symmetric (E_rel τ)
  := E_rel_symmetric' V_rel_symmetric.
Instance A_rel_symmetric {τ} : Symmetric (A_rel τ)
  := A_rel_symmetric' V_rel_symmetric.

Instance G_rel_symmetric {Γ} : Symmetric (G_rel Γ).
Proof.
  repeat intro.
  apply V_rel_symmetric.
  eapply H; eassumption.
Qed.

Instance rel_expr_symmetric {Γ τ} : Symmetric (related_exprs Γ τ).
Proof.
  intros e0 e1 He.
  destruct He.
  refine (mk_related_exprs He1 He0 _).
  intros ρ1 ρ0 Hρ.
  symmetry.
  apply He.
  symmetry.
  exact Hρ.
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
  intros ? x y z.
  intros [Hx Hy Hxy].
  intros [Hy' Hz Hyz].
  exists Hx Hz.
  pose proof tc_unique Hy' Hy.
  subst.

  intros.
  transitivity (μ Hy A0); auto.
  apply Hxy.
  transitivity A1; [| symmetry]; exact H0.
Qed.

Instance V_rel_transitive {τ} :
  Transitive (V_rel τ).
Proof.
  induction τ; repeat intro. {
    destruct x using Val_rect; try contradiction H.
    destruct y using Val_rect; try contradiction H.
    destruct z using Val_rect; try contradiction H0.
    transitivity (v_real r0); auto.
  } {
    destruct x using Val_rect; try contradiction H.
    destruct y using Val_rect; try contradiction H.
    destruct z using Val_rect; try contradiction H0.
    destruct H as [[? ?] [? [? ?]]].
    destruct H0 as [[? ?] [? [? ?]]].
    repeat subst.
    split; auto.
    do 2 (eexists; eauto).
    intros va0 va1 Hva.
    transitivity (body0.[va0 : Expr/]); auto.
    apply H.
    transitivity va1; [| symmetry]; assumption.
  }
Qed.

Instance E_rel_transitive {τ} : Transitive (E_rel τ)
  := E_rel_transitive' V_rel_transitive.
Instance A_rel_transitive {τ} : Transitive (A_rel τ)
  := A_rel_transitive' V_rel_transitive.

Instance G_rel_transitive {Γ} : Transitive (G_rel Γ).
Proof.
  intros ρ0 ρ1 ρ2 Hρ0ρ1 Hρ1ρ2 x v0 v2 τ Γx ρ0x ρ2x.
  destruct (env_search (WT_Env_tc ρ0) Γx) as [v0' ρ0x'].
  destruct (env_search (WT_Env_tc ρ1) Γx) as [v1 ρ1x].
  destruct (env_search (WT_Env_tc ρ2) Γx) as [v2' ρ2x'].
  rewrite ρ0x' in ρ0x.
  rewrite ρ2x' in ρ2x.
  inversion ρ0x.
  inversion ρ2x.
  subst.

  transitivity v1. {
    eapply Hρ0ρ1; eauto.
  } {
    eapply Hρ1ρ2; eauto.
  }
Qed.

Instance rel_expr_transitive {Γ τ} : Transitive (related_exprs Γ τ).
Proof.
  intros e0 e1 e2 He0e1 He1e2.
  destruct He0e1 as [He0 He1 He0e1].
  destruct He1e2 as [He1' He2 He1e2].
  pose proof (tc_unique He1' He1); subst.

  split; auto.
  intros ρ0 ρ2.
  transitivity (e1.[subst_of_WT_Env ρ0]). {
    apply He0e1.
    transitivity ρ2; [| symmetry]; exact Hρ.
  } {
    apply He1e2.
    exact Hρ.
  }
Qed.


(* Reflexivity *)

(* the reflexivity depends on the fundamental property. Also, reflexivity is
   mostly only on well-typed values, so we can't always build a `Reflexive`
   class instance. *)

(* Two versions of sub-identity for A_rel. They're essentially the same, but one
   is sometimes easier to apply than the other. *)
Lemma A_rel_subidentity {τ} {A0 A1 : Event Val}
  : A_rel τ A0 A1 ->
    forall v : WT_Val τ,
      A0 v = A1 v.
Proof.
  intros.
  apply A_rels_equiv; auto.
  apply fundamental_property_of_values.
  apply v.
Qed.

Lemma A_rel_subidentity' τ {A0 A1 : Event (WT_Val τ)}
  : A_rel τ (narrow_event A0) (narrow_event A1) ->
    A0 = A1.
Proof.
  intros.
  extensionality v.
  rewrite <- (narrow_cast_inverse τ A0).
  rewrite <- (narrow_cast_inverse τ A1).
  apply A_rel_subidentity.
  auto.
Qed.

Lemma E_rel_reflexive {τ e} :
  (TC · ⊢ e : τ) ->
  E_rel τ e e.
Proof.
  intros.
  destruct (fundamental_property X).
  specialize (He _ _ G_rel_nil).
  unfold subst_of_WT_Env in He.
  simpl in He.
  rewrite subst_id in He.
  exact He.
Qed.

Instance V_rel_reflexive {τ} :
  @Reflexive (WT_Val τ) (V_rel τ).
Proof.
  intros [v Hv].
  apply fundamental_property_of_values; auto.
Qed.

Instance G_rel_reflexive {Γ} : Reflexive (G_rel Γ).
Proof.
  intros ρ x v0 v1 τ Γx ρx ρx'.
  repeat intro.
  rewrite ρx in ρx'.
  inversion ρx'.
  destruct (env_search (WT_Env_tc ρ) Γx).
  pose proof V_rel_reflexive x0.
  simpl in H.
  rewrite e in ρx.
  inversion ρx.
  subst v0 v1.
  exact H.
Qed.