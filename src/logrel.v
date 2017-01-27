Require Import Reals.
Require Import List.
Require Import Ensembles.
Require Import Coq.Logic.JMeq.
Require Import utils.
Require Import syntax.

Local Open Scope ennr.

(* Sketches of binary and unary logical relations for our language as a ML-like
   functor. *)

(* The unary relations are all in Type, while the binary ones are in Prop. This
   is simply because that's how they're used. It would be nice to make it
   user-selectable, but I'm not sure how without lots of copy/paste. *)

Module Log_rel1.
  Definition rel X := X -> Type.

  Module Type BASE.
    Parameter (V_rel_real : rel (val ℝ)).
    Parameter (E_rel' : forall τ (v_rel_τ : rel (val τ)), rel (expr · τ)).
  End BASE.

  Module Defs (Base : BASE).
    Export Base.

    Inductive V_rel_arrow {τa τr}
              (V_rel_a : rel (val τa))
              (V_rel_r : rel (val τr))
      : rel (val (τa ~> τr)) :=
    | mk_V_rel_arrow
        (body : expr (τa :: ·) τr) :
        (forall va,
            V_rel_a va ->
            E_rel' τr V_rel_r (proj1_sig (ty_subst1 body va))) ->
        V_rel_arrow V_rel_a V_rel_r (v_lam body).

    Fixpoint V_rel τ : rel (val τ) :=
      match τ with
      | ℝ => V_rel_real
      | (τa ~> τr) => V_rel_arrow (V_rel τa) (V_rel τr)
      end.

    Definition E_rel : forall τ, rel (expr · τ) := fun τ => E_rel' τ (V_rel τ).

    Definition G_rel Γ (ρ : wt_env Γ) :=
      dep_env_allT V_rel ρ.

    Definition expr_rel Γ τ (e : expr Γ τ) : Type :=
      forall ρ,
        G_rel Γ ρ ->
        E_rel τ (proj1_sig (close ρ e)).
  End Defs.

  Module Type CASES (Base : BASE).
    Module Defs := Defs Base.
    Export Defs.

    Parameters
      (* seems redundant to have all 3 of these... *)
      (case_val : forall τ v,
          V_rel τ v -> E_rel τ v)
      (case_real : forall r,
          E_rel ℝ (e_real r))
      (case_lam : forall τa τr body,
          (forall v,
              V_rel τa v ->
              E_rel τr (proj1_sig (ty_subst1 body v))) ->
          E_rel (τa ~> τr) (e_lam body))
      (case_app : forall τa τr ef ea,
          E_rel (τa ~> τr) ef ->
          E_rel τa ea ->
          E_rel τr (e_app ef ea))
      (case_factor : forall e,
          E_rel ℝ e ->
          E_rel ℝ (e_factor e))
      (case_sample :
         E_rel ℝ e_sample)
      (case_plus : forall el er,
          E_rel ℝ el ->
          E_rel ℝ er ->
          E_rel ℝ (e_plus el er)).
  End CASES.

  Module Compatibility (Base : BASE) (Cases : CASES Base).
    Import Cases.

    Lemma apply_G_rel {Γ ρ} :
      G_rel Γ ρ ->
      forall {x τ} {v : val τ},
        lookup Γ x = Some τ ->
        erase v = erase_wt_env ρ x ->
        V_rel τ v.
    Proof.
      intros.
      revert Γ ρ H H0 X.
      induction x; intros. {
        dep_destruct (Γ, H0).
        dep_destruct (ρ, H).
        destruct X.

        cbn in *.
        elim_erase_eqs.
        apply val_eq in x.
        subst.
        auto.
      } {
        dep_destruct (Γ, H0).
        dep_destruct (ρ, H).
        destruct X.
        eapply IHx; eauto.
      }
    Qed.

    Local Ltac common :=
      intros;
      intros ρ Hρ;
      repeat match goal with
             | [ H : expr_rel _ _ _ |- _ ] =>
               specialize (H ρ Hρ)
             end;
      elim_sig_exprs;
      try elim_erase_eqs.

    Lemma compat_real Γ r :
      expr_rel Γ ℝ (e_real r).
    Proof.
      common.
      apply case_real.
    Qed.

    Lemma compat_var Γ τ x H :
      expr_rel Γ τ (e_var x H).
    Proof.
      common.

      destruct (env_search_subst ρ H) as [v ρx].

      pose proof (apply_G_rel Hρ H ρx).
      elim_erase_eqs.

      apply case_val.
      assumption.
    Qed.

    Lemma compat_lam Γ τa τr body :
      expr_rel (τa :: Γ) τr body ->
      expr_rel Γ (τa ~> τr) (e_lam body).
    Proof.
      common.
      rewrite rewrite_v_lam.
      apply case_val.
      constructor.
      intros.
      elim_sig_exprs.
      rewrite H0 in He0; clear e H0.

      specialize (X (dep_cons va ρ)).
      elim_sig_exprs.
      asimpl in He0.
      elim_erase_eqs.
      apply X.
      exact (X0, Hρ).
    Qed.

    Lemma compat_app Γ τa τr ef ea :
      expr_rel Γ (τa ~> τr) ef ->
      expr_rel Γ τa ea ->
      expr_rel Γ τr (e_app ef ea).
    Proof.
      common.
      apply case_app; auto.
    Qed.

    Lemma compat_factor Γ e :
      expr_rel Γ ℝ e ->
      expr_rel Γ ℝ (e_factor e).
    Proof.
      common.
      apply case_factor; auto.
    Qed.

    Lemma compat_sample Γ :
      expr_rel Γ ℝ e_sample.
    Proof.
      common.
      apply case_sample.
    Qed.

    Lemma compat_plus Γ el er :
      expr_rel Γ ℝ el ->
      expr_rel Γ ℝ er ->
      expr_rel Γ ℝ (e_plus el er).
    Proof.
      common.
      apply case_plus; auto.
    Qed.

    Lemma fundamental_property {Γ τ} e :
      expr_rel Γ τ e.
    Proof.
      induction e.
      - apply compat_real.
      - apply compat_var.
      - apply compat_lam; auto.
      - apply compat_app; auto.
      - apply compat_factor; auto.
      - apply compat_sample.
      - apply compat_plus; auto.
    Qed.
  End Compatibility.
End Log_rel1.

Module Log_rel2.
  Definition rel X := X -> X -> Prop.

  Module Type BASE.
    Parameter (V_rel_real : rel (val ℝ)).
    Parameter (E_rel' : forall τ (v_rel_τ : rel (val τ)), rel (expr · τ)).
  End BASE.

  Module Defs (Base : BASE).
    Export Base.

    Inductive V_rel_arrow {τa τr}
              (V_rel_a : rel (val τa))
              (V_rel_r : rel (val τr))
      : rel (val (τa ~> τr)) :=
    | mk_V_rel_arrow
        (body0 body1 : expr (τa :: ·) τr) :
        (forall va0 va1,
            V_rel_a va0 va1 ->
            E_rel' τr V_rel_r
                   (proj1_sig (ty_subst1 body0 va0))
                   (proj1_sig (ty_subst1 body1 va1))) ->
        V_rel_arrow V_rel_a V_rel_r
                    (v_lam body0)
                    (v_lam body1).

    Fixpoint V_rel τ : rel (val τ) :=
      match τ with
      | ℝ => V_rel_real
      | (τa ~> τr) => V_rel_arrow (V_rel τa) (V_rel τr)
      end.

    Definition E_rel : forall τ, rel (expr · τ) := fun τ => E_rel' τ (V_rel τ).

    Inductive G_rel : forall Γ, rel (wt_env Γ) :=
    | G_rel_nil : G_rel · dep_nil dep_nil
    | G_rel_cons {τ Γ v0 v1 ρ0 ρ1} :
        V_rel τ v0 v1 -> G_rel Γ ρ0 ρ1 ->
        G_rel (τ :: Γ) (dep_cons v0 ρ0) (dep_cons v1 ρ1).

    Definition expr_rel Γ τ : rel (expr Γ τ) :=
      fun e0 e1 =>
        forall ρ0 ρ1,
          G_rel Γ ρ0 ρ1 ->
          E_rel τ (proj1_sig (close ρ0 e0)) (proj1_sig (close ρ1 e1)).
  End Defs.

  Module Type CASES (Base : BASE).
    Module Defs := Defs Base.
    Export Defs.

    Parameters
      (case_val : forall τ v0 v1,
          V_rel τ v0 v1 -> E_rel τ v0 v1)
      (case_real : forall r,
          E_rel ℝ (e_real r) (e_real r))
      (case_lam : forall τa τr body0 body1,
          (forall v0 v1,
              V_rel τa v0 v1 ->
              E_rel τr
                    (proj1_sig (ty_subst1 body0 v0))
                    (proj1_sig (ty_subst1 body1 v1))) ->
          E_rel (τa ~> τr) (e_lam body0) (e_lam body1))
      (case_app : forall τa τr ef0 ef1 ea0 ea1,
          E_rel (τa ~> τr) ef0 ef1 ->
          E_rel τa ea0 ea1 ->
          E_rel τr (e_app ef0 ea0) (e_app ef1 ea1))
      (case_factor : forall e0 e1,
          E_rel ℝ e0 e1 ->
          E_rel ℝ (e_factor e0) (e_factor e1))
      (case_sample :
         E_rel ℝ e_sample e_sample)
      (case_plus : forall el0 el1 er0 er1,
          E_rel ℝ el0 el1 ->
          E_rel ℝ er0 er1 ->
          E_rel ℝ (e_plus el0 er0) (e_plus el1 er1)).
  End CASES.

  Module Compatibility (Base : BASE) (Cases : CASES Base).
    Import Cases.

    Lemma apply_G_rel {Γ ρ0 ρ1} :
      G_rel Γ ρ0 ρ1 ->
      forall {x τ} {v0 v1 : val τ},
        lookup Γ x = Some τ ->
        erase v0 = erase_wt_env ρ0 x ->
        erase v1 = erase_wt_env ρ1 x ->
        V_rel τ v0 v1.
    Proof.
      intros.
      revert Γ ρ0 ρ1 H H0 H1 H2.
      induction x; intros. {
        dep_destruct (Γ, H0).
        dep_destruct (ρ0, ρ1, H).

        cbn in *.
        elim_erase_eqs.
        apply val_eq in H1.
        apply val_eq in H2.
        subst.
        auto.
      } {
        dep_destruct (Γ, H0).
        dep_destruct (ρ0, ρ1, H).
        eapply IHx; eauto.
      }
    Qed.

    Local Ltac common :=
      intros;
      intros ρ0 ρ1 Hρ;
      repeat match goal with
             | [ H : expr_rel _ _ _ _ |- _ ] =>
               specialize (H ρ0 ρ1 Hρ)
             end;
      elim_sig_exprs;
      try elim_erase_eqs.

    Lemma compat_real Γ r :
      expr_rel Γ ℝ (e_real r) (e_real r).
    Proof.
      common.
      apply case_real.
    Qed.

    Lemma compat_var Γ τ x H :
      expr_rel Γ τ (e_var x H) (e_var x H).
    Proof.
      common.

      destruct (env_search_subst ρ0 H) as [v0 ρ0x].
      destruct (env_search_subst ρ1 H) as [v1 ρ1x].

      pose proof (apply_G_rel Hρ H ρ0x ρ1x).
      elim_erase_eqs.

      apply case_val.
      assumption.
    Qed.

    Lemma compat_lam Γ τa τr body0 body1 :
      expr_rel (τa :: Γ) τr body0 body1 ->
      expr_rel Γ (τa ~> τr) (e_lam body0) (e_lam body1).
    Proof.
      common.
      rewrite 2 rewrite_v_lam.
      apply case_val.
      constructor.
      intros.
      elim_sig_exprs.
      rewrite H2 in He1; clear e H2.
      rewrite H1 in He2; clear e0 H1.

      specialize (H (dep_cons va0 ρ0) (dep_cons va1 ρ1)).
      elim_sig_exprs.
      asimpl in He1.
      asimpl in He2.
      elim_erase_eqs.
      apply H.
      constructor; auto.
    Qed.

    Lemma compat_app Γ τa τr ef0 ea0 ef1 ea1 :
      expr_rel Γ (τa ~> τr) ef0 ef1 ->
      expr_rel Γ τa ea0 ea1 ->
      expr_rel Γ τr (e_app ef0 ea0) (e_app ef1 ea1).
    Proof.
      common.
      apply case_app; auto.
    Qed.

    Lemma compat_factor Γ e0 e1 :
      expr_rel Γ ℝ e0 e1 ->
      expr_rel Γ ℝ (e_factor e0) (e_factor e1).
    Proof.
      common.
      apply case_factor; auto.
    Qed.

    Lemma compat_sample Γ :
      expr_rel Γ ℝ e_sample e_sample.
    Proof.
      common.
      apply case_sample.
    Qed.

    Lemma compat_plus Γ el0 el1 er0 er1 :
      expr_rel Γ ℝ el0 el1 ->
      expr_rel Γ ℝ er0 er1 ->
      expr_rel Γ ℝ (e_plus el0 er0) (e_plus el1 er1).
    Proof.
      common.
      apply case_plus; auto.
    Qed.

    Lemma fundamental_property :
      forall {Γ τ} e, expr_rel Γ τ e e.
    Proof.
      induction e.
      - apply compat_real.
      - apply compat_var.
      - apply compat_lam; auto.
      - apply compat_app; auto.
      - apply compat_factor; auto.
      - apply compat_sample.
      - apply compat_plus; auto.
    Qed.
  End Compatibility.
End Log_rel2.