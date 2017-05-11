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
    Parameter (E_rel' : forall τ ϕ (v_rel_τ : rel (val τ)), rel (expr · τ ϕ)).
  End BASE.

  Module Defs (Base : BASE).
    Export Base.

    Inductive V_rel_arrow {τa ϕ τr}
              (V_rel_a : rel (val τa))
              (V_rel_r : rel (val τr))
      : rel (val (τa ~~ ϕ ~> τr)) :=
    | mk_V_rel_arrow
        (body : expr (τa :: ·) τr ϕ) :
        (forall va,
            V_rel_a va ->
            E_rel' τr _ V_rel_r (proj1_sig (ty_subst1 body va))) ->
        V_rel_arrow V_rel_a V_rel_r (v_lam body).

    Fixpoint V_rel τ : rel (val τ) :=
      match τ with
      | ℝ => V_rel_real
      | (τa ~~ ϕ ~> τr) => V_rel_arrow (V_rel τa) (V_rel τr)
      end.

    Definition E_rel : forall τ ϕ, rel (expr · τ ϕ) :=
      fun τ ϕ => E_rel' τ ϕ (V_rel τ).

    Definition G_rel Γ (ρ : wt_env Γ) :=
      dep_env_allT V_rel ρ.

    Definition expr_rel Γ τ ϕ (e : expr Γ τ ϕ) : Type :=
      forall ρ,
        G_rel Γ ρ ->
        E_rel τ _ (proj1_sig (close ρ e)).
  End Defs.

  Module Type CASES (Base : BASE).
    Module Defs := Defs Base.
    Export Defs.

    Parameters
      (* seems redundant to have all 3 of these... *)
      (case_val : forall τ v,
          V_rel τ v -> E_rel τ _ v)
      (case_real : forall r,
          E_rel ℝ _ (e_real r))
      (case_lam : forall τa ϕ τr body,
          (forall v,
              V_rel τa v ->
              E_rel τr _ (proj1_sig (ty_subst1 body v))) ->
          E_rel (τa ~~ ϕ ~> τr) _ (e_lam body))
      (case_app : forall τa ϕ τr ϕf ϕa ef ea,
          E_rel (τa ~~ ϕ ~> τr) ϕf ef ->
          E_rel τa ϕa ea ->
          E_rel τr _ (e_app ef ea))
      (case_factor : forall ϕ e,
          E_rel ℝ ϕ e ->
          E_rel ℝ _ (e_factor e))
      (case_sample :
         E_rel ℝ _ e_sample)
      (case_observe : forall ϕ0 e0 e1,
         E_rel ℝ ϕ0 e0 ->
         E_rel ℝ _ e1 ->
         E_rel ℝ _ (e_observe e0 e1))
      (case_unop : forall ϕ op e,
          E_rel ℝ ϕ e ->
          E_rel ℝ _ (e_unop op e))
      (case_binop : forall ϕl ϕr ϕ op Hϕ el er,
          E_rel ℝ ϕl el ->
          E_rel ℝ ϕr er ->
          E_rel ℝ ϕ (e_binop op Hϕ el er))
      (case_hide : forall e,
          E_rel ℝ ObsR e ->
          E_rel ℝ ObsNone (e_hide_observable e)).
  End CASES.

  Module Compatibility (Base : BASE) (Cases : CASES Base).
    Import Cases.

    Lemma apply_G_rel {Γ ρ} :
      G_rel Γ ρ ->
      forall {x τ v},
        lookup Γ x = Some τ ->
        dep_lookup ρ x = Some (existT _ τ v) ->
        V_rel τ v.
    Proof.
      intros.
      revert Γ ρ H H0 X.
      induction x; intros. {
        destruct ρ; inversion H; subst.
        simpl in *.
        dependent destruction H0.
        destruct X.
        auto.
      } {
        destruct ρ; inversion H; subst.
        simpl in *.
        eapply IHx; eauto.
        destruct X.
        auto.
      }
    Qed.

    Local Ltac common :=
      intros;
      intros ρ Hρ;
      repeat match goal with
             | [ H : expr_rel _ _ _ _ |- _ ] =>
               specialize (H ρ Hρ)
             end;
      elim_sig_exprs;
      try elim_erase_eqs.

    Lemma compat_real Γ r :
      expr_rel Γ ℝ _ (e_real r).
    Proof.
      common.
      apply case_real.
    Qed.

    Lemma compat_var Γ τ x H :
      expr_rel Γ τ _ (e_var x H).
    Proof.
      common.

      destruct (env_search ρ H) as [v ρv].
      pose proof (lookup_subst _ ρv).
      elim_erase_eqs.

      apply case_val.
      eapply apply_G_rel; eauto.
    Qed.

    Lemma compat_lam Γ τa ϕ τr body :
      expr_rel (τa :: Γ) τr _ body ->
      expr_rel Γ (τa ~~ ϕ ~> τr) _ (e_lam body).
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

    Lemma compat_app Γ τa ϕ τr ϕf ef ϕa ea :
      expr_rel Γ (τa ~~ ϕ ~> τr) ϕf ef ->
      expr_rel Γ τa ϕa ea ->
      expr_rel Γ τr _ (e_app ef ea).
    Proof.
      common.
      apply case_app; auto.
    Qed.


    Lemma compat_factor Γ ϕ e :
      expr_rel Γ ℝ ϕ e ->
      expr_rel Γ ℝ _ (e_factor e).
    Proof.
      common.
      apply case_factor; auto.
    Qed.

    Lemma compat_sample Γ :
      expr_rel Γ ℝ _ e_sample.
    Proof.
      common.
      apply case_sample.
    Qed.

    Lemma compat_observe Γ ϕ0 e0 e1 :
      expr_rel Γ ℝ ϕ0 e0 ->
      expr_rel Γ ℝ _ e1 ->
      expr_rel Γ ℝ _ (e_observe e0 e1).
    Proof.
      common.
      apply case_observe; auto.
    Qed.

    Lemma compat_unop Γ op ϕ e :
      expr_rel Γ ℝ ϕ e ->
      expr_rel Γ ℝ _ (e_unop op e).
    Proof.
      common.
      apply case_unop; auto.
    Qed.

    Lemma compat_binop Γ ϕl ϕr ϕ op Hϕ el er :
      expr_rel Γ ℝ ϕl el ->
      expr_rel Γ ℝ ϕr er ->
      expr_rel Γ ℝ ϕ (e_binop op Hϕ el er).
    Proof.
      common.
      apply case_binop; auto.
    Qed.

    Lemma compat_hide Γ e :
      expr_rel Γ ℝ ObsR e ->
      expr_rel Γ ℝ ObsNone (e_hide_observable e).
    Proof.
      common.
      apply case_hide; auto.
    Qed.

    Lemma fundamental_property {Γ τ ϕ} e :
      expr_rel Γ τ ϕ e.
    Proof.
      induction e.
      - apply compat_real.
      - apply compat_var.
      - apply compat_lam; auto.
      - apply compat_app; auto.
      - apply compat_factor; auto.
      - apply compat_sample.
      - apply compat_observe; auto.
      - apply compat_unop; auto.
      - apply compat_binop; auto.
      - apply compat_hide; auto.
    Qed.
  End Compatibility.
End Log_rel1.

(* Literally copy paste with one word changed *)
Module Log_rel1_prop.
  Definition rel X := X -> Prop.

  Module Type BASE.
    Parameter (V_rel_real : rel (val ℝ)).
    Parameter (E_rel' : forall τ ϕ (v_rel_τ : rel (val τ)), rel (expr · τ ϕ)).
  End BASE.

  Module Defs (Base : BASE).
    Export Base.

    Inductive V_rel_arrow {τa ϕ τr}
              (V_rel_a : rel (val τa))
              (V_rel_r : rel (val τr))
      : rel (val (τa ~~ ϕ ~> τr)) :=
    | mk_V_rel_arrow
        (body : expr (τa :: ·) τr ϕ) :
        (forall va,
            V_rel_a va ->
            E_rel' τr _ V_rel_r (proj1_sig (ty_subst1 body va))) ->
        V_rel_arrow V_rel_a V_rel_r (v_lam body).

    Fixpoint V_rel τ : rel (val τ) :=
      match τ with
      | ℝ => V_rel_real
      | (τa ~~ ϕ ~> τr) => V_rel_arrow (V_rel τa) (V_rel τr)
      end.

    Definition E_rel : forall τ ϕ, rel (expr · τ ϕ) :=
      fun τ ϕ => E_rel' τ ϕ (V_rel τ).

    Definition G_rel Γ (ρ : wt_env Γ) :=
      dep_env_allT V_rel ρ.

    Definition expr_rel Γ τ ϕ (e : expr Γ τ ϕ) : Type :=
      forall ρ,
        G_rel Γ ρ ->
        E_rel τ _ (proj1_sig (close ρ e)).
  End Defs.

  Module Type CASES (Base : BASE).
    Module Defs := Defs Base.
    Export Defs.

    Parameters
      (* seems redundant to have all 3 of these... *)
      (case_val : forall τ v,
          V_rel τ v -> E_rel τ _ v)
      (case_real : forall r,
          E_rel ℝ _ (e_real r))
      (case_lam : forall τa ϕ τr body,
          (forall v,
              V_rel τa v ->
              E_rel τr _ (proj1_sig (ty_subst1 body v))) ->
          E_rel (τa ~~ ϕ ~> τr) _ (e_lam body))
      (case_app : forall τa ϕ τr ϕf ϕa ef ea,
          E_rel (τa ~~ ϕ ~> τr) ϕf ef ->
          E_rel τa ϕa ea ->
          E_rel τr _ (e_app ef ea))
      (case_factor : forall ϕ e,
          E_rel ℝ ϕ e ->
          E_rel ℝ _ (e_factor e))
      (case_sample :
         E_rel ℝ _ e_sample)
      (case_observe : forall ϕ0 e0 e1,
         E_rel ℝ ϕ0 e0 ->
         E_rel ℝ _ e1 ->
         E_rel ℝ _ (e_observe e0 e1))
      (case_unop : forall ϕ op e,
          E_rel ℝ ϕ e ->
          E_rel ℝ _ (e_unop op e))
      (case_binop : forall ϕl ϕr ϕ op Hϕ el er,
          E_rel ℝ ϕl el ->
          E_rel ℝ ϕr er ->
          E_rel ℝ ϕ (e_binop op Hϕ el er))
      (case_hide : forall e,
          E_rel ℝ ObsR e ->
          E_rel ℝ ObsNone (e_hide_observable e)).
  End CASES.

  Module Compatibility (Base : BASE) (Cases : CASES Base).
    Import Cases.

    Lemma apply_G_rel {Γ ρ} :
      G_rel Γ ρ ->
      forall {x τ v},
        lookup Γ x = Some τ ->
        dep_lookup ρ x = Some (existT _ τ v) ->
        V_rel τ v.
    Proof.
      intros.
      revert Γ ρ H H0 X.
      induction x; intros. {
        destruct ρ; inversion H; subst.
        simpl in *.
        dependent destruction H0.
        destruct X.
        auto.
      } {
        destruct ρ; inversion H; subst.
        simpl in *.
        eapply IHx; eauto.
        destruct X.
        auto.
      }
    Qed.

    Local Ltac common :=
      intros;
      intros ρ Hρ;
      repeat match goal with
             | [ H : expr_rel _ _ _ _ |- _ ] =>
               specialize (H ρ Hρ)
             end;
      elim_sig_exprs;
      try elim_erase_eqs.

    Lemma compat_real Γ r :
      expr_rel Γ ℝ _ (e_real r).
    Proof.
      common.
      apply case_real.
    Qed.

    Lemma compat_var Γ τ x H :
      expr_rel Γ τ _ (e_var x H).
    Proof.
      common.

      destruct (env_search ρ H) as [v ρv].
      pose proof (lookup_subst _ ρv).
      elim_erase_eqs.

      apply case_val.
      eapply apply_G_rel; eauto.
    Qed.

    Lemma compat_lam Γ τa ϕ τr body :
      expr_rel (τa :: Γ) τr _ body ->
      expr_rel Γ (τa ~~ ϕ ~> τr) _ (e_lam body).
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
      exact (H, Hρ).
    Qed.

    Lemma compat_app Γ τa ϕ τr ϕf ef ϕa ea :
      expr_rel Γ (τa ~~ ϕ ~> τr) ϕf ef ->
      expr_rel Γ τa ϕa ea ->
      expr_rel Γ τr _ (e_app ef ea).
    Proof.
      common.
      apply case_app; auto.
    Qed.


    Lemma compat_factor Γ ϕ e :
      expr_rel Γ ℝ ϕ e ->
      expr_rel Γ ℝ _ (e_factor e).
    Proof.
      common.
      apply case_factor; auto.
    Qed.

    Lemma compat_sample Γ :
      expr_rel Γ ℝ _ e_sample.
    Proof.
      common.
      apply case_sample.
    Qed.

    Lemma compat_observe Γ ϕ0 e0 e1 :
      expr_rel Γ ℝ ϕ0 e0 ->
      expr_rel Γ ℝ _ e1 ->
      expr_rel Γ ℝ _ (e_observe e0 e1).
    Proof.
      common.
      apply case_observe; auto.
    Qed.

    Lemma compat_unop Γ op ϕ e :
      expr_rel Γ ℝ ϕ e ->
      expr_rel Γ ℝ _ (e_unop op e).
    Proof.
      common.
      apply case_unop; auto.
    Qed.

    Lemma compat_binop Γ ϕl ϕr ϕ op Hϕ el er :
      expr_rel Γ ℝ ϕl el ->
      expr_rel Γ ℝ ϕr er ->
      expr_rel Γ ℝ ϕ (e_binop op Hϕ el er).
    Proof.
      common.
      apply case_binop; auto.
    Qed.

    Lemma compat_hide Γ e :
      expr_rel Γ ℝ ObsR e ->
      expr_rel Γ ℝ ObsNone (e_hide_observable e).
    Proof.
      common.
      apply case_hide; auto.
    Qed.

    Lemma fundamental_property {Γ τ ϕ} e :
      expr_rel Γ τ ϕ e.
    Proof.
      induction e.
      - apply compat_real.
      - apply compat_var.
      - apply compat_lam; auto.
      - apply compat_app; auto.
      - apply compat_factor; auto.
      - apply compat_sample.
      - apply compat_observe; auto.
      - apply compat_unop; auto.
      - apply compat_binop; auto.
      - apply compat_hide; auto.
    Qed.
  End Compatibility.
End Log_rel1_prop.

Module Log_rel2.
  Definition rel X := X -> X -> Prop.

  Module Type BASE.
    Parameter (V_rel_real : rel (val ℝ)).
    Parameter (E_rel' : forall τ ϕ (v_rel_τ : rel (val τ)), rel (expr · τ ϕ)).
  End BASE.

  Module Defs (Base : BASE).
    Export Base.

    Inductive V_rel_arrow {τa ϕ τr}
              (V_rel_a : rel (val τa))
              (V_rel_r : rel (val τr))
      : rel (val (τa ~~ ϕ ~> τr)) :=
    | mk_V_rel_arrow
        (body0 body1 : expr (τa :: ·) τr ϕ) :
        (forall va0 va1,
            V_rel_a va0 va1 ->
            E_rel' τr _ V_rel_r
                   (proj1_sig (ty_subst1 body0 va0))
                   (proj1_sig (ty_subst1 body1 va1))) ->
        V_rel_arrow V_rel_a V_rel_r
                    (v_lam body0)
                    (v_lam body1).

    Fixpoint V_rel τ : rel (val τ) :=
      match τ with
      | ℝ => V_rel_real
      | (τa ~~ ϕ ~> τr) => V_rel_arrow (V_rel τa) (V_rel τr)
      end.

    Definition E_rel : forall τ ϕ , rel (expr · τ ϕ) :=
      fun τ ϕ  => E_rel' τ ϕ (V_rel τ).

    Inductive G_rel : forall Γ, rel (wt_env Γ) :=
    | G_rel_nil : G_rel · dep_nil dep_nil
    | G_rel_cons {τ Γ v0 v1 ρ0 ρ1} :
        V_rel τ v0 v1 -> G_rel Γ ρ0 ρ1 ->
        G_rel (τ :: Γ) (dep_cons v0 ρ0) (dep_cons v1 ρ1).

    Definition expr_rel Γ τ ϕ : rel (expr Γ τ ϕ) :=
      fun e0 e1 =>
        forall ρ0 ρ1,
          G_rel Γ ρ0 ρ1 ->
          E_rel τ ϕ (proj1_sig (close ρ0 e0)) (proj1_sig (close ρ1 e1)).
  End Defs.

  Module Type CASES (Base : BASE).
    Module Defs := Defs Base.
    Export Defs.

    Parameters
      (case_val : forall τ v0 v1,
          V_rel τ v0 v1 -> E_rel τ _ v0 v1)
      (case_real : forall r,
          E_rel ℝ _ (e_real r) (e_real r))
      (case_lam : forall τa ϕ τr body0 body1,
          (forall v0 v1,
              V_rel τa v0 v1 ->
              E_rel τr _
                    (proj1_sig (ty_subst1 body0 v0))
                    (proj1_sig (ty_subst1 body1 v1))) ->
          E_rel (τa ~~ ϕ ~> τr) _ (e_lam body0) (e_lam body1))
      (case_app : forall τa ϕ τr ϕf ϕa ef0 ef1 ea0 ea1,
          E_rel (τa ~~ ϕ ~> τr) ϕf ef0 ef1 ->
          E_rel τa ϕa ea0 ea1 ->
          E_rel τr _ (e_app ef0 ea0) (e_app ef1 ea1))
      (case_factor : forall ϕ e0 e1,
          E_rel ℝ ϕ e0 e1 ->
          E_rel ℝ _ (e_factor e0) (e_factor e1))
      (case_sample :
         E_rel ℝ _ e_sample e_sample)
      (case_observe : forall ϕl el0 el1 er0 er1,
         E_rel ℝ ϕl el0 el1 ->
         E_rel ℝ _ er0 er1 ->
         E_rel ℝ _ (e_observe el0 er0) (e_observe el1 er1))
      (case_unop : forall op ϕ e0 e1,
          E_rel ℝ ϕ e0 e1 ->
          E_rel ℝ _ (e_unop op e0) (e_unop op e1))
      (case_binop : forall ϕl ϕr ϕ op Hϕ el0 el1 er0 er1,
          E_rel ℝ ϕl el0 el1 ->
          E_rel ℝ ϕr er0 er1 ->
          E_rel ℝ ϕ (e_binop op Hϕ el0 er0) (e_binop op Hϕ el1 er1))
      (case_hide : forall e0 e1,
          E_rel ℝ ObsR e0 e1 ->
          E_rel ℝ ObsNone (e_hide_observable e0) (e_hide_observable e1)).
  End CASES.

  Module Compatibility (Base : BASE) (Cases : CASES Base).
    Import Cases.

    Lemma apply_G_rel {Γ ρ0 ρ1} :
      G_rel Γ ρ0 ρ1 ->
      forall {x τ v0 v1},
        lookup Γ x = Some τ ->
        dep_lookup ρ0 x = Some (existT _ τ v0) ->
        dep_lookup ρ1 x = Some (existT _ τ v1) ->
        V_rel τ v0 v1.
    Proof.
      intros.
      revert Γ ρ0 ρ1 H H0 H1 H2.
      induction x; intros. {
        d_destruct (ρ0, ρ1); inversion H0; subst.
        simpl in *.
        d_destruct H1.
        d_destruct H.
        assumption.
      } {
        d_destruct (ρ0, ρ1); inversion H0; subst.
        cbn in *.
        d_destruct H.
        eapply IHx; eauto.
      }
    Qed.

    Local Ltac common :=
      intros;
      intros ρ0 ρ1 Hρ;
      repeat match goal with
             | [ H : expr_rel _ _ _ _ _ |- _ ] =>
               specialize (H ρ0 ρ1 Hρ)
             end;
      elim_sig_exprs;
      try elim_erase_eqs.

    Lemma compat_real Γ r :
      expr_rel Γ ℝ _ (e_real r) (e_real r).
    Proof.
      common.
      apply case_real.
    Qed.

    Lemma compat_var Γ τ x H :
      expr_rel Γ τ _ (e_var x H) (e_var x H).
    Proof.
      common.

      destruct (env_search ρ0 H) as [v0 ρv0].
      destruct (env_search ρ1 H) as [v1 ρv1].
      pose proof (lookup_subst _ ρv0).
      pose proof (lookup_subst _ ρv1).
      elim_erase_eqs.

      apply case_val.
      eapply apply_G_rel; eauto.
    Qed.

    Lemma compat_lam Γ τa ϕ τr body0 body1 :
      expr_rel (τa :: Γ) τr _ body0 body1 ->
      expr_rel Γ (τa ~~ ϕ ~> τr) _ (e_lam body0) (e_lam body1).
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

    Lemma compat_app Γ τa ϕ τr ϕf ef0 ef1 ϕa ea0 ea1 :
      expr_rel Γ (τa ~~ ϕ ~> τr) ϕf ef0 ef1 ->
      expr_rel Γ τa ϕa ea0 ea1 ->
      expr_rel Γ τr _ (e_app ef0 ea0) (e_app ef1 ea1).
    Proof.
      common.
      apply case_app; auto.
    Qed.

    Lemma compat_factor Γ ϕ e0 e1 :
      expr_rel Γ ℝ ϕ e0 e1 ->
      expr_rel Γ ℝ _ (e_factor e0) (e_factor e1).
    Proof.
      common.
      apply case_factor; auto.
    Qed.

    Lemma compat_sample Γ :
      expr_rel Γ ℝ _ e_sample e_sample.
    Proof.
      common.
      apply case_sample.
    Qed.

    Lemma compat_observe Γ ϕl el0 el1 er0 er1 :
      expr_rel Γ ℝ ϕl el0 el1 ->
      expr_rel Γ ℝ _ er0 er1 ->
      expr_rel Γ ℝ _ (e_observe el0 er0) (e_observe el1 er1).
    Proof.
      common.
      apply case_observe; auto.
    Qed.

    Lemma compat_unop Γ op ϕ e0 e1 :
      expr_rel Γ ℝ ϕ e0 e1 ->
      expr_rel Γ ℝ _ (e_unop op e0) (e_unop op e1).
    Proof.
      common.
      apply case_unop; auto.
    Qed.

    Lemma compat_binop Γ ϕl ϕr ϕ op Hϕ el0 el1 er0 er1 :
      expr_rel Γ ℝ ϕl el0 el1 ->
      expr_rel Γ ℝ ϕr er0 er1 ->
      expr_rel Γ ℝ ϕ (e_binop op Hϕ el0 er0) (e_binop op Hϕ el1 er1).
    Proof.
      intros.
      intros ρ0 ρ1 Hρ.
      repeat match goal with
             | [ H : expr_rel _ _ _ _ _ |- _ ] =>
               specialize (H ρ0 ρ1 Hρ)
             end.
      elim_sig_exprs.

      expr_destruct e3; try solve [inversion He3].
      expr_destruct e4; inject He4.
      inject He3.

      assert (ϕl0 = ϕl /\ ϕl1 = ϕl /\ ϕr0 = ϕr /\ ϕr1 = ϕr). {
        repeat split;
          eapply proj2;
          eapply expr_type_unique;
          etransitivity; try eassumption;
            eauto.
      }
      destruct H1 as [? [? [? ?]]]; subst.
      elim_erase_eqs.
      d_destruct (Hϕ0, Hϕ1).

      apply case_binop; auto.
    Qed.

    Lemma compat_hide Γ e0 e1 :
      expr_rel Γ ℝ ObsR e0 e1 ->
      expr_rel Γ ℝ ObsNone (e_hide_observable e0) (e_hide_observable e1).
    Proof.
      common.
      apply case_hide; auto.
    Qed.

    Lemma fundamental_property :
      forall {Γ τ ϕ} e, expr_rel Γ τ ϕ e e.
    Proof.
      induction e.
      - apply compat_real.
      - apply compat_var.
      - apply compat_lam; auto.
      - apply compat_app; auto.
      - apply compat_factor; auto.
      - apply compat_sample.
      - apply compat_observe; auto.
      - apply compat_unop; auto.
      - apply compat_binop; auto.
      - apply compat_hide; auto.
    Qed.
  End Compatibility.
End Log_rel2.