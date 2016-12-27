(* Tested with coq 8.5pl1 *)

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
Import EqNotations.
Require Import determinism.
Require Import logrel.
Require Export integration.

Local Open Scope ennr.

Definition ev {τ} (e : expr · τ) σ : option (val τ) :=
  match eval_dec e σ with
  | eval_dec_ex_unique v w _ _ => Some v
  | eval_dec_not_ex _ => None
  end.

Definition ew {τ} (e : expr · τ) σ : R+ :=
  match eval_dec e σ with
  | eval_dec_ex_unique v w _ _ => w
  | eval_dec_not_ex _ => 0
  end.

Definition eval_in {τ} (e : expr · τ) σ : Meas (val τ) :=
  fun A =>
    option0 (indicator A <$> ev e σ) * ew e σ.

Definition μ {τ} (e : expr · τ) : Meas (val τ) :=
  μEntropy >>= eval_in e.

Ltac fold_μ :=
  match goal with
  | [ |- context [ μEntropy >>= eval_in ?e ] ] => fold (μ e)
  | [ H : context [ μEntropy >>= eval_in ?e ] |- _ ] => fold (μ e)
  end.

Theorem μe_eq_μEntropy :
  forall {τ B} (e : expr · τ)
         (f : val τ -> Meas B),
    μ e >>= f =
    μEntropy >>=
             (fun σ A =>
                option0 ((fun v => f v A) <$> ev e σ) * ew e σ).
Proof.
  intros.

  unfold μ, ">>=".

  extensionality A.

  rewrite riemann_def_of_lebesgue_integration.
  rewrite tonelli_sigma_finite; auto.
  unfold eval_in.

  integrand_extensionality σ.

  rewrite <- integration_linear_mult_r.
  f_equal.

  destruct (ev _ _); simpl. {
    setoid_rewrite integration_of_indicator.
    apply lebesgue_pos_measure_interval.
  } {
    setoid_replace 0 with (0 * 0) by ring.
    rewrite <- integration_linear_mult_r.
    ring.
  }
Qed.

Ltac econtradict e := exfalso; eapply e; repeat econstructor; eauto.

Ltac what_equality_am_I_proving :=
  match goal with
  | [ |- @eq ?t ?l ?r ] => idtac "proving" l "=" r "at type" t
  | _ => idtac "it doesn't look like your goal is an equality"
  end.

Ltac decide_eval' e σ v w ex u :=
  let not_ex := fresh "not_ex" in
  let focus_ev := fresh "focus_ev" in
  let focus_ew := fresh "focus_ew" in
  set (focus_ev := ev e σ);
  set (focus_ew := ew e σ);
  unfold ev in focus_ev;
  unfold ew in focus_ew;
  destruct (eval_dec e σ) as [v w ex u | not_ex];
  subst focus_ev focus_ew;
  [| try solve [ econtradict not_ex
               | ennr
               | ring]
  ].

Tactic Notation "decide_eval" "as"
       "[" ident(v) ident(w) ident(ex) ident(u) "]"
  := match goal with
     | [ |- context[ev ?e ?σ] ] => decide_eval' e σ v w ex u
     end.
Tactic Notation "decide_eval" constr(e) constr(σ) "as"
       "[" ident(v) ident(w) ident(ex) ident(u) "]"
  :=  decide_eval' e σ v w ex u.

(* used to push the option0 into the very inside *)
Lemma μe_eq_μEntropy2 {τ0 τ1 B}
      (f : val τ0 -> val τ1 -> Meas B)
      (e0 : expr · τ0) (e1 : expr · τ1) :
  μ e0 >>= (fun v0 => μ e1 >>= (fun v1 => f v0 v1)) =
  μEntropy >>=
           (fun σ0 =>
              μEntropy >>=
                       (fun σ1 A =>
                          option0 ((fun v0 v1 => f v0 v1 A)
                                     <$> ev e0 σ0 <*> ev e1 σ1)
                                  * ew e1 σ1 * ew e0 σ0)).
Proof.
  extensionality A.
  setoid_rewrite μe_eq_μEntropy; eauto.
  rewrite μe_eq_μEntropy.
  integrand_extensionality σ0.

  unfold ">>=".
  rewrite <- integration_linear_mult_r.
  f_equal.

  decide_eval as [v0 w0 ex0 u0]; simpl; auto.
  rewrite <- integration_linear_mult_l.
  ring.
Qed.


Import Log_rel2.
Module CtxEquivBase <: BASE.

  Definition V_rel_real : rel (val ℝ) := eq.

  Definition A_rel' (τ : Ty) (V_rel_τ : rel (val τ)) : rel (Event (val τ)) :=
    fun A0 A1 =>
      forall v0 v1 (Hv : V_rel_τ v0 v1),
        (A0 v0 = (* iff *) A1 v1).

  Definition E_rel' (τ : Ty) (V_rel_τ : rel (val τ)) : rel (expr · τ) :=
    fun e0 e1 =>
      forall A0 A1 (HA : A_rel' τ V_rel_τ A0 A1),
        μ e0 A0 = μ e1 A1.
End CtxEquivBase.

Module CtxEquivCases <: CASES CtxEquivBase.
  Module Defs := Defs CtxEquivBase.
  Export Defs.

  Definition A_rel τ := A_rel' τ (V_rel τ).

  Notation "'EXP' Γ ⊢ e0 ≈ e1 : τ" :=
    (expr_rel Γ τ e0 e1)
      (at level 69, e0 at level 99, e1 at level 99, no associativity).

  Lemma val_is_atomic {τ} (v : val τ) A σ :
    eval_in v σ A =
    indicator A v.
  Proof.
    unfold eval_in.

    decide_eval as [v' w ex u]; simpl. {
      destruct (invert_eval_val ex).
      subst.
      ring.
    }
  Qed.

  Lemma val_is_dirac {τ} (v : val τ) :
    μ v = dirac v.
  Proof.
    extensionality A.
    unfold μ, dirac; simpl.
    apply int_const_entropy; intro σ.
    erewrite val_is_atomic.
    reflexivity.
  Qed.

  Lemma case_val : forall τ v0 v1,
      V_rel τ v0 v1 -> E_rel τ v0 v1.
  Proof.
    repeat intro.
    destruct_val v0; subst; destruct_val v1; cbn in *. {
      inject H.

      rewrite rewrite_v_real.

      rewrite val_is_dirac.
      unfold dirac, indicator; simpl.
      f_equal.
      apply HA.
      reflexivity.
    } {
      d_destruct H.

      rewrite 2 rewrite_v_lam.
      rewrite 2 val_is_dirac.

      unfold dirac, indicator; simpl.
      f_equal.
      apply HA.

      constructor; auto.
    }
  Qed.

  Lemma case_real : forall r,
      E_rel ℝ (e_real r) (e_real r).
  Proof.
    intros.

    rewrite rewrite_v_real.
    apply case_val.
    reflexivity.
  Qed.

  Lemma case_lam : forall τa τr body0 body1,
      (forall v0 v1,
          V_rel τa v0 v1 ->
          E_rel τr
                (proj1_sig (ty_subst1 body0 v0))
                (proj1_sig (ty_subst1 body1 v1))) ->
      E_rel (τa ~> τr) (e_lam body0) (e_lam body1).
  Proof.
    intros.
    rewrite 2 rewrite_v_lam.
    apply case_val.
    constructor; auto.
  Qed.

  Definition apply_in {τa τr}
             (vf : val (τa ~> τr))
             (va : val τa)
             (σ : Entropy)
    : Meas (val τr) :=
    val_arrow_rect
      (const (Meas (val τr)))
      (fun body => eval_in (proj1_sig (ty_subst1 body va)) σ)
      vf.

  (* ugly, ugly proof, relies on internals of WT_Val_arrow_rect *)
  Lemma elim_apply_in {τa τr} (body : expr (τa :: ·) τr) :
    forall (va : val τa),
      apply_in (v_lam body) va =
      eval_in (proj1_sig (ty_subst1 body va)).
  Proof.
    intros.

    extensionality σ.
    simpl.
    unfold solution_left, solution_right, simplification_heq.
    unfold eq_rect_r.
    simpl.

    replace (eq_sym _) with (@eq_refl _ (e_lam body)); auto.
    apply UIP_dec.
    apply expr_eq_dec.
  Qed.

  (* ok, let's never look inside apply_in ever again. It's too ugly *)
  Global Opaque apply_in.

  Lemma by_μe_eq_μEntropy_app {τa τr}
        (ef : expr · (τa ~> τr))
        (ea : expr · τa) :
    μ (e_app ef ea) =
    μ ef >>= (fun vf => μ ea >>= (fun va => μEntropy >>= apply_in vf va)).
  Proof.
    extensionality A.

    rewrite μe_eq_μEntropy2.
    set (x σf σa σbody A :=
           option0 ((fun vf va => apply_in vf va σbody A)
                      <$> ev ef σf
                      <*> ev ea σa)
           * ew ea σa * ew ef σf).
    transitivity ((μEntropy >>= (fun σ => x (π 0 σ) (π 1 σ) (π 2 σ))) A). {
      subst x.
      simpl.

      integrand_extensionality σ.

      unfold eval_in.
      decide_eval (e_app ef ea) σ as [vr wr exr ur]; simpl. {
        d_destruct exr; try absurd_val.
        rename va into va'.
        decide_eval ef (π 0 σ) as [vf wf exf uf].
        decide_eval ea (π 1 σ) as [va wa exa ua].
        simpl.

        destruct_val vf.
        rewrite elim_apply_in.

        destruct (uf _ _ exr1), (ua _ _ exr2); subst.
        d_destruct H.

        unfold eval_in.

        decide_eval as [vr' wr' exr' ur'].
        destruct (ur' _ _ exr3); subst.
        simpl.
        ring.
      } {
        decide_eval ef (π 0 σ) as [vf wf exf uf].
        decide_eval ea (π 1 σ) as [va wa exa ua].
        simpl.

        destruct_val vf.
        rewrite elim_apply_in.

        unfold eval_in.

        decide_eval as [v5 w5 ex5 u5].
        econtradict not_ex.
      }
    } {
      rewrite pick_3_entropies.
      integrand_extensionality σf.
      integrand_extensionality σa.
      subst x.
      simpl.
      unfold ">>=".
      rewrite <- 2 integration_linear_mult_r.
      do 2 f_equal.

      decide_eval ef σf as [vf wf exf uf]; simpl. {
        decide_eval ea σa as [va wa exa ua]; simpl; auto.
        apply int_const_entropy; auto.
      } {
        apply int_const_entropy; auto.
      }
    }
  Qed.


  Lemma case_app : forall τa τr ef0 ef1 ea0 ea1,
      E_rel (τa ~> τr) ef0 ef1 ->
      E_rel τa ea0 ea1 ->
      E_rel τr (e_app ef0 ea0) (e_app ef1 ea1).
  Proof.
    repeat intro.

    do 2 rewrite by_μe_eq_μEntropy_app.

    apply (coarsening (A_rel (τa ~> τr))); auto.
    intros B vf0 vf1 Hvf.
    unfold preimage.
    f_equal.

    apply (coarsening (A_rel τa)); auto.
    intros B0 va0 va1 Hva.
    unfold preimage.
    f_equal.

    destruct_val vf0.
    destruct_val vf1.

    destruct Hvf as [? ? Hvf].
    clear body body0.

    specialize (Hvf va0 va1 Hva A0 A1 HA).
    rewrite 2 elim_apply_in.

    apply Hvf.
  Qed.

  Definition factor_in (v : val ℝ) : Meas (val ℝ) :=
    fun A =>
      match (v : expr · ℝ) with
      | e_real r =>
        match Rle_dec 0 r with
        | left rpos => indicator A (v_real r) * finite r rpos
        | _ => 0
        end
      | _ => 0
      end.

  Lemma by_μe_eq_μEntropy_factor (e : expr · ℝ) :
    μ (e_factor e) =
    μ e >>= factor_in.
  Proof.
    extensionality A.

    rewrite μe_eq_μEntropy.

    integrand_extensionality σ.
    unfold eval_in.

    decide_eval (e_factor e) σ as [vr wr exr ur]; simpl. {
      destruct_val vr.
      d_destruct exr; try absurd_val.

      decide_eval as [ve we exe ue].
      destruct (ue _ _ exr); subst.

      unfold factor_in; simpl.
      destruct Rle_dec; [| contradiction].
      replace (finite r r0) with (finite r rpos) by ennr.
      ring.
    } {
      decide_eval as [ve we exe ue].
      destruct_val ve.
      unfold factor_in; simpl.

      destruct Rle_dec; [| solve [ring]].
      econtradict not_ex.
      Unshelve.
      auto.
    }
  Qed.

  Lemma case_factor : forall e0 e1,
      E_rel ℝ e0 e1 ->
      E_rel ℝ (e_factor e0) (e_factor e1).
  Proof.
    repeat intro.

    rewrite 2 by_μe_eq_μEntropy_factor.

    apply (coarsening (A_rel ℝ)); auto.
    intros B v0 v1 Hv.
    unfold preimage.
    f_equal.

    destruct_val v0.
    destruct_val v1.
    simpl in *.
    d_destruct Hv.

    unfold factor_in; simpl.
    destruct Rle_dec; auto.

    unfold indicator.
    do 2 f_equal.
    apply HA.
    reflexivity.
  Qed.

  Lemma case_sample :
    E_rel ℝ e_sample e_sample.
  Proof.
    repeat intro.
    f_equal.
    extensionality v.

    apply HA.
    reflexivity.
  Qed.

  Definition plus_in (v v' : val ℝ) : Meas (val ℝ) :=
    match (v : expr · ℝ), (v' : expr · ℝ) with
    | e_real r, e_real r' => fun A => indicator A (v_real (r + r'))
    | _, _ => fun A => 0
    end.

  Lemma by_μe_eq_μEntropy_plus (el er : expr · ℝ) :
    μ (e_plus el er) =
    μ el >>= (fun vl => μ er >>= (fun vr => plus_in vl vr)).
  Proof.
    extensionality A.

    rewrite μe_eq_μEntropy2.
    set (f σ0 σ1 A :=
           option0 (((fun vl vr => plus_in vl vr A) <$> ev el σ0) <*> ev er σ1)
           * ew er σ1 * ew el σ0).
    transitivity ((μEntropy >>= (fun σ => f (π 0 σ) (π 1 σ))) A). {
      subst f.
      simpl.

      integrand_extensionality σ.

      unfold eval_in.
      decide_eval (e_plus el er) σ as [v0 w0 ex0 u0]. {
        dependent destruction ex0; try absurd_val.
        decide_eval el (π 0 σ) as [vl wl exl ul].
        decide_eval er (π 1 σ) as [vr wr exr ur].
        destruct_val vr.
        destruct_val vl.
        simpl.

        destruct (ul _ _ ex0_1), (ur _ _ ex0_2); subst.
        d_destruct (H, H1).

        unfold plus_in; simpl.
        ring.
      } {
        decide_eval el (π 0 σ) as [vl wl exl ul].
        decide_eval er (π 1 σ) as [vr wr exr ur].
        destruct_val vr.
        destruct_val vl.
        econtradict not_ex.
      }
    } {
      rewrite pick_2_entropies.
      auto.
    }
  Qed.


  Lemma case_plus : forall el0 el1 er0 er1,
      E_rel ℝ el0 el1 ->
      E_rel ℝ er0 er1 ->
      E_rel ℝ (e_plus el0 er0) (e_plus el1 er1).
  Proof.
    repeat intro.

    do 2 rewrite by_μe_eq_μEntropy_plus.

    apply (coarsening (A_rel ℝ)); auto.
    intros B vl0 vl1 Hvl.
    unfold preimage.
    f_equal.

    apply (coarsening (A_rel ℝ)); auto.
    intros B0 vr0 vr1 Hvr.
    unfold preimage.
    f_equal.

    destruct_val vl0.
    destruct_val vl1.
    destruct_val vr0.
    destruct_val vr1.

    hnf in Hvl, Hvr.
    d_destruct (Hvl, Hvr).
    unfold plus_in; simpl.

    unfold indicator.
    f_equal.
    apply HA.
    reflexivity.
  Qed.
End CtxEquivCases.

Module CtxEquivCompat := Compatibility CtxEquivBase CtxEquivCases.
Export CtxEquivCases CtxEquivCompat.

Print Assumptions fundamental_property.

Lemma fundamental_property_of_values {τ} (v : val τ) :
  V_rel τ v v.
Proof.
  intros.

  destruct v using wt_val_rect; subst; simpl in *. {
    reflexivity.
  } {
    constructor.
    repeat intro.

    pose proof fundamental_property _ _ body as fp.
    specialize (fp _ _ (G_rel_cons H G_rel_nil)).

    elim_sig_exprs.
    elim_erase_eqs.

    apply fp; auto.
  }
Qed.
