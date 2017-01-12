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

Definition ev {τ ϕ} (e : expr · τ ϕ) σ : option (val τ) :=
  match eval_dec e σ with
  | eval_dec_ex_unique v w _ _ => Some v
  | eval_dec_not_ex _ => None
  end.

Definition ew {τ ϕ} (e : expr · τ ϕ) σ : R+ :=
  match eval_dec e σ with
  | eval_dec_ex_unique v w _ _ => w
  | eval_dec_not_ex _ => 0
  end.

Definition eval_in {τ ϕ} (e : expr · τ ϕ) σ : Meas (val τ) :=
  fun A =>
    option0 (indicator A <$> ev e σ) * ew e σ.

Definition μ {τ ϕ} (e : expr · τ ϕ) : Meas (val τ) :=
  μEntropy >>= eval_in e.

Definition obs_ew (e : expr · ℝ ObsR) (v : val ℝ) σ : R+ :=
  match obs_eval_dec e σ v with
  | obs_eval_dec_ex_unique w _ _ => w
  | obs_eval_dec_not_ex _ => 0
  end.

Definition obs_μ (e : expr · ℝ ObsR) (v : val ℝ) : Meas unit :=
  fun A => integration (fun σ => indicator A tt * obs_ew e v σ) μEntropy.

Ltac fold_μ :=
  match goal with
  | [ |- context [ μEntropy >>= eval_in ?e ] ] => fold (μ e)
  | [ H : context [ μEntropy >>= eval_in ?e ] |- _ ] => fold (μ e)
  end.

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

Theorem μe_eq_μEntropy :
  forall {τ ϕ B} (e : expr · τ ϕ)
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

(* used to push the option0 into the very inside *)
Lemma μe_eq_μEntropy2 {τ0 ϕ0 τ1 ϕ1 B}
      (f : val τ0 -> val τ1 -> Meas B)
      (e0 : expr · τ0 ϕ0) (e1 : expr · τ1 ϕ1) :
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

(* A subset of things that can be tonellied *)
(* TODO: figure out exactly what's needed to make this not a whitelist *)
Inductive interchangable : forall {A}, Meas A -> Type :=
| interchangable_μ {τ ϕ} (e : expr · τ ϕ) : interchangable (μ e)
| interchangable_sig_fi {A} (m : Meas A) : SigmaFinite m -> interchangable m
.
Hint Constructors interchangable.

Lemma tonelli_μ_and_finite {τ ϕ B C}
      (μFin : Meas B)
      (f : val τ -> B -> Meas C)
      (e : expr · τ ϕ) :
  SigmaFinite μFin ->
  μ e >>= (fun x => μFin >>= (fun y => f x y)) =
  μFin >>= (fun y => μ e >>= (fun x => f x y)).
Proof.
  intros.

  extensionality A.

  rewrite μe_eq_μEntropy.
  setoid_rewrite μe_eq_μEntropy.
  setoid_rewrite tonelli_sigma_finite; auto.
  unfold ">>=".
  integrand_extensionality σ0.
  decide_eval as [v0 w0 ex0 u0]. {
    simpl.
    apply integration_linear_mult_r.
  } {
    simpl.
    rewrite <- integration_linear_mult_r.
    ring.
  }
Qed.

Lemma tonelli
      {A B C} (μ0 : Meas A) (μ1 : Meas B)
      (f : A -> B -> Meas C) :
  interchangable μ0 ->
  interchangable μ1 ->
  μ0 >>= (fun x0 => μ1 >>= (fun x1 => f x0 x1)) =
  μ1 >>= (fun x1 => μ0 >>= (fun x0 => f x0 x1)).
Proof.
  intros.

  extensionality ev.
  d_destruct (X, X0). {
    rewrite !μe_eq_μEntropy2.
    setoid_rewrite tonelli_sigma_finite at 1; auto.
    integrand_extensionality σ0.
    integrand_extensionality σ1.

    decide_eval as [v0 w0 ex0 u0].
    decide_eval as [v1 w1 ex1 u1].
    simpl.
    ring.
  } {
    rewrite tonelli_μ_and_finite; auto.
  } {
    rewrite tonelli_μ_and_finite; auto.
  } {
    apply tonelli_sigma_finite; auto.
  }
Qed.

Import Log_rel2.
Module CtxEquivBase <: BASE.

  Definition V_rel_real : rel (val ℝ) := eq.

  Definition A_rel' (τ : Ty) (V_rel_τ : rel (val τ)) : rel (Event (val τ)) :=
    fun A0 A1 =>
      forall v0 v1 (Hv : V_rel_τ v0 v1),
        (A0 v0 = (* iff *) A1 v1).

  Definition E_rel' (τ : Ty) (ϕ : Effect) (V_rel_τ : rel (val τ)) : rel (expr · τ ϕ) :=
    fun e0 e1 =>
      (forall A0 A1 (HA : A_rel' τ V_rel_τ A0 A1),
          μ e0 A0 = μ e1 A1) /\
      forall (Hτ : τ = ℝ) (Hϕ : ϕ = ObsR) (v : val ℝ) A,
        (* `v' could be written as 2 sepearte related values, but it's unnecessary at base type *)
        let e0' := (rew [expr · ℝ] Hϕ in rew [fun t => expr · t ϕ] Hτ in e0) in
        let e1' := (rew [expr · ℝ] Hϕ in rew [fun t => expr · t ϕ] Hτ in e1) in
        obs_μ e0' v A = obs_μ e1' v A.
End CtxEquivBase.

Module CtxEquivCases <: CASES CtxEquivBase.
  Module Defs := Defs CtxEquivBase.
  Export Defs.

  Definition A_rel τ := A_rel' τ (V_rel τ).

  Notation "'EXP' Γ ⊢ e0 ≈ e1 : τ , ϕ" :=
    (expr_rel Γ τ ϕ e0 e1)
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
      V_rel τ v0 v1 -> E_rel τ _ v0 v1.
  Proof.
    split; [| discriminate]; intros.
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
      E_rel ℝ _ (e_real r) (e_real r).
  Proof.
    intros.

    rewrite rewrite_v_real.
    apply case_val.
    reflexivity.
  Qed.

  Lemma case_lam : forall τa ϕ τr body0 body1,
      (forall v0 v1,
          V_rel τa v0 v1 ->
          E_rel τr _
                (proj1_sig (ty_subst1 body0 v0))
                (proj1_sig (ty_subst1 body1 v1))) ->
      E_rel (τa ~~ ϕ ~> τr) _ (e_lam body0) (e_lam body1).
  Proof.
    intros.
    rewrite 2 rewrite_v_lam.
    apply case_val.
    constructor; auto.
  Qed.

  Definition apply_in {τa ϕ τr}
             (vf : val (τa ~~ ϕ ~> τr))
             (va : val τa)
             (σ : Entropy)
    : Meas (val τr) :=
    val_arrow_rect
      (const (Meas (val τr)))
      (fun body => eval_in (proj1_sig (ty_subst1 body va)) σ)
      vf.

  (* ugly, ugly proof, relies on internals of WT_Val_arrow_rect *)
  Lemma elim_apply_in {τa ϕ τr} (body : expr (τa :: ·) τr ϕ) :
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

  Lemma by_μe_eq_μEntropy_app {τa ϕ τr ϕf ϕa}
        (ef : expr · (τa ~~ ϕ ~> τr) ϕf)
        (ea : expr · τa ϕa) :
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

  Definition obs_apply_in {τa}
             (vf : val (τa ~~ ObsR ~> ℝ))
             (va : val τa)
             (v : val ℝ)
             (σ : Entropy)
    : Meas unit :=
    val_arrow_rect
      (const (Meas unit))
      (fun body A => indicator A tt * obs_ew (proj1_sig (ty_subst1 body va)) v σ)
      vf.

  (* ugly, ugly proof, relies on internals of WT_Val_arrow_rect *)
  Lemma elim_obs_apply_in {τa} (body : expr (τa :: ·) ℝ ObsR) :
      obs_apply_in (v_lam body) =
      fun va v σ A => indicator A tt * obs_ew (proj1_sig (ty_subst1 body va)) v σ.
  Proof.
    intros.

    unfold obs_apply_in.
    cbn.
    unfold solution_left, solution_right, simplification_heq.
    unfold eq_rect_r.
    simpl.

    replace (eq_sym _) with (@eq_refl _ (e_lam body)); auto.
    apply UIP_dec.
    apply expr_eq_dec.
  Qed.

  (* ok, let's never look inside apply_in ever again. It's too ugly *)
  Global Opaque obs_apply_in.

  Lemma obs_help_app {τa ϕf ϕa}
        (ef : expr · (τa ~~ ObsR ~> ℝ) ϕf)
        (ea : expr · τa ϕa)
        (v : val ℝ) :
    obs_μ (e_app ef ea) v =
    μ ef >>=
      (fun vf =>
         μ ea >>=
           (fun va =>
              μEntropy >>= obs_apply_in vf va v)).
  Proof.
    extensionality A.

    rewrite μe_eq_μEntropy2.
    set (x σf σa σbody A :=
           option0 ((fun vf va => obs_apply_in vf va v σbody A)
                      <$> ev ef σf
                      <*> ev ea σa)
           * ew ea σa * ew ef σf).

    transitivity ((μEntropy >>= (fun σ => x (π 0 σ) (π 1 σ) (π 2 σ))) A). {
      subst x.
      simpl.

      integrand_extensionality σ.

      unfold obs_ew.
      destruct obs_eval_dec as [wr exr ur | not_ex]. {
        d_destruct exr; try absurd_val.
        rename va into va'.
        decide_eval ef (π 0 σ) as [vf wf exf uf].
        decide_eval ea (π 1 σ) as [va wa exa ua].
        cbn.

        destruct_val vf.
        rewrite elim_obs_apply_in.

        destruct (uf _ _ e), (ua _ _ e0); subst.
        d_destruct H.

        ring_simplify.
        f_equal.

        unfold obs_ew.
        destruct obs_eval_dec as [wr' exr' ur' | not_ex]. {
          destruct (ur' _ exr); subst.
          auto.
        } {
          contradict (not_ex _ exr).
        }
      } {
        decide_eval ef (π 0 σ) as [vf wf exf uf].
        decide_eval ea (π 1 σ) as [va wa exa ua].
        simpl.

        destruct_val vf.
        rewrite elim_obs_apply_in.

        unfold obs_ew.
        destruct obs_eval_dec; try ring.
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

  Lemma case_app : forall τa ϕ τr ϕf ϕa ef0 ef1 ea0 ea1,
      E_rel (τa ~~ ϕ ~> τr) ϕf ef0 ef1 ->
      E_rel τa ϕa ea0 ea1 ->
      E_rel τr ϕ (e_app ef0 ea0) (e_app ef1 ea1).
  Proof.
    split; intros. {
      rewrite 2 by_μe_eq_μEntropy_app.

      apply (coarsening (A_rel _)); [apply H; tauto |].
      intros B vf0 vf1 Hvf.
      unfold preimage.
      f_equal.

      apply (coarsening (A_rel τa)); [apply H0; tauto |].
      intros B0 va0 va1 Hva.
      unfold preimage.
      f_equal.

      destruct_val vf0.
      destruct_val vf1.

      destruct Hvf as [? ? Hvf].

      rewrite 2 elim_apply_in.

      apply Hvf; auto.
    } {
      subst.
      subst e0' e1'.
      cbn.

      rewrite 2 obs_help_app.

      apply (coarsening (A_rel _)); [apply H; tauto |].
      intros B vf0 vf1 Hvf.
      unfold preimage.
      f_equal.

      apply (coarsening (A_rel τa)); [apply H0; tauto |].
      intros B0 va0 va1 Hva.
      unfold preimage.
      f_equal.

      destruct_val vf0.
      destruct_val vf1.

      destruct Hvf as [? ? Hvf].
      rewrite 2 elim_obs_apply_in.

      destruct (Hvf _ _ Hva) as [_ Hvf'].
      specialize (Hvf' eq_refl eq_refl v A).
      cbn in Hvf'.
      apply Hvf'.
    }
  Qed.

  Definition factor_in (v : val ℝ) : Meas (val ℝ) :=
    fun A =>
      match (v : expr _ _ _) with
      | e_real r =>
        match Rle_dec 0 r with
        | left rpos => indicator A (v_real r) * finite r rpos
        | _ => 0
        end
      | _ => 0
      end.

  Lemma by_μe_eq_μEntropy_factor {ϕ} (e : expr · ℝ ϕ) :
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

  Lemma case_factor : forall ϕ e0 e1,
      E_rel ℝ ϕ e0 e1 ->
      E_rel ℝ ObsNone (e_factor e0) (e_factor e1).
  Proof.
    split; [| discriminate]; intros.

    rewrite 2 by_μe_eq_μEntropy_factor.

    apply (coarsening (A_rel ℝ)); [apply H; tauto |].
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
    E_rel ℝ ObsR e_sample e_sample.
  Proof.
    split; intros. {
      f_equal.
      extensionality v.

      apply HA.
      reflexivity.
    } {
      reflexivity.
    }
  Qed.

  Lemma by_μe_eq_μEntropy_observe
        {ϕl}
        (el : expr · ℝ ϕl)
        (er : expr · ℝ ObsR) :
    μ (e_observe el er) =
    μ el >>= (fun v A => indicator A v * obs_μ er v full_event).
  Proof.
    extensionality A.

    rewrite μe_eq_μEntropy.

    set (f σ0 σ1 A :=
           option0 ((fun vl => indicator A vl * obs_ew er vl σ1) <$> ev el σ0) * ew el σ0).
    transitivity ((μEntropy >>= (fun σ => f (π 0 σ) (π 1 σ))) A). {
      subst f.
      cbn.

      integrand_extensionality σ.
      unfold eval_in.
      decide_eval (e_observe el er) σ as [v w E u]. {
        d_destruct E; try absurd_val.
        decide_eval as [vl wl El ul].
        specialize (ul _ _ E).
        inject ul.

        cbn.
        unfold obs_ew.
        destruct obs_eval_dec. {
          specialize (u0 _ e).
          subst.
          ring.
        } {
          econtradict not_ex.
        }
      } {
        decide_eval as [vl wl El ul].
        cbn.
        unfold obs_ew.
        destruct obs_eval_dec; try ring.
        econtradict not_ex.
      }
    } {
      rewrite pick_2_entropies.
      subst f.

      f_equal.
      extensionality σ0.
      clear A.
      extensionality A.
      unfold obs_μ, ">>=".
      rewrite <- integration_linear_mult_r.
      f_equal.
      destruct (ev el σ0); cbn. {
        rewrite <- !integration_linear_mult_l.
        ring.
      } {
        apply int_const_entropy; auto.
      }
    }
  Qed.

  Lemma case_observe : forall ϕl el0 el1 er0 er1,
      E_rel ℝ ϕl el0 el1 ->
      E_rel ℝ _ er0 er1 ->
      E_rel ℝ _ (e_observe el0 er0) (e_observe el1 er1).
  Proof.
    split; [| discriminate]; intros.
    repeat intro.

    do 2 rewrite by_μe_eq_μEntropy_observe.

    apply (coarsening (A_rel ℝ)); [apply H; tauto |].
    intros B vl0 vl1 Hvl.
    unfold preimage.
    f_equal.

    unfold indicator.
    rewrite (HA vl0 vl1 Hvl).
    f_equal.

    destruct_val vl0.
    destruct_val vl1.
    inject Hvl.

    destruct H0 as [_ ?].
    specialize (H0 eq_refl eq_refl (v_real r0)).
    cbn in H0.
    rewrite H0.
    auto.
  Qed.

  Definition op_in (op : binop) (v v' : val ℝ) : Meas (val ℝ) :=
    match (v : expr _ _ _), (v' : expr _ _ _) with
    | e_real r, e_real r' => fun A => indicator A (v_real (δ op r r'))
    | _, _ => fun A => 0
    end.

  Lemma by_μe_eq_μEntropy_op (op : binop)
        {ϕl ϕr}
        (el : expr · ℝ ϕl)
        (er : expr · ℝ ϕr) :
    μ (e_binop op el er) =
    μ el >>= (fun vl => μ er >>= (fun vr => op_in op vl vr)).
  Proof.
    extensionality A.

    rewrite μe_eq_μEntropy2.
    set (f σ0 σ1 A :=
           option0 (((fun vl vr => op_in op vl vr A) <$> ev el σ0) <*> ev er σ1)
           * ew er σ1 * ew el σ0).
    transitivity ((μEntropy >>= (fun σ => f (π 0 σ) (π 1 σ))) A). {
      subst f.
      simpl.

      integrand_extensionality σ.

      unfold eval_in.
      decide_eval (e_binop op el er) σ as [v0 w0 ex0 u0]. {
        dependent destruction ex0; try absurd_val.
        decide_eval el (π 0 σ) as [vl wl exl ul].
        decide_eval er (π 1 σ) as [vr wr exr ur].
        destruct_val vr.
        destruct_val vl.
        simpl.

        destruct (ul _ _ ex0_1), (ur _ _ ex0_2); subst.
        d_destruct (H, H1).

        unfold op_in; simpl.
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

  Definition obs_op_in (op : binop) (vl : val ℝ) (er : expr · ℝ ObsR)
             (v : val ℝ) σ
    : Meas unit :=
    match (vl : expr _ _ _), (v : expr _ _ _) with
    | e_real rl, e_real rv =>
      match δ_unique_inv op rv rl with
      | Some ri =>
        fun A =>
          indicator A tt
          * obs_ew er (v_real ri) σ
          / ennr_abs (δ_partial_deriv_2 op rl ri)
      | None => const 0
      end
    | _, _ => const 0
    end.

  Lemma obs_help_op {ϕl} op
        (el : expr · ℝ ϕl)
        (er : expr · ℝ ObsR)
        (v : val ℝ) :
    obs_μ (e_binop op el er) v =
    μ el >>= (fun vl => μEntropy >>= obs_op_in op vl er v).
  Proof.
    extensionality A.

    rewrite μe_eq_μEntropy.
    set (f σl σr A :=
           option0 ((fun vl => obs_op_in op vl er v σr A)
                      <$> ev el σl)
           * ew el σl).
    transitivity ((μEntropy >>= (fun σ => f (π 0 σ) (π 1 σ))) A). {
      subst f.
      simpl.

      integrand_extensionality σ.

      unfold obs_ew.
      destruct obs_eval_dec as [w E u | not_ex]. {
        d_destruct E; try absurd_val.
        decide_eval el (π 0 σ) as [vl wl exl ul].
        destruct_val vl.
        cbn.

        unfold ennr_div.
        specialize (ul _ _ e).
        inject ul.
        d_destruct H.

        rewrite e2.
        enough (w1 = obs_ew er (v_real r1) (π 1 σ)) by (subst; ring).

        unfold obs_ew.
        destruct is_v1.
        destruct obs_eval_dec as [wr' exr' ur' | not_ex]. {
          destruct (ur' _ E); subst.
          auto.
        } {
          econtradict not_ex.
        }
      } {
        decide_eval el (π 0 σ) as [vl wl exl ul].
        cbn.

        destruct_val vl.
        destruct_val v.
        cbn.
        remember (δ_unique_inv _ _ _).
        destruct o; unfold const; try ring.

        unfold obs_ew, ennr_div.
        destruct obs_eval_dec; try ring.
        econtradict not_ex.
      }
    } {
      rewrite pick_2_entropies.
      integrand_extensionality σl.
      subst f.
      simpl.
      unfold ">>=".
      rewrite <- integration_linear_mult_r.
      destruct ev; cbn; auto.
      f_equal.
      apply int_const_entropy; auto.
    }
  Qed.

  Lemma case_binop : forall op ϕl ϕr el0 el1 er0 er1,
      E_rel ℝ ϕl el0 el1 ->
      E_rel ℝ ϕr er0 er1 ->
      E_rel ℝ _ (e_binop op el0 er0) (e_binop op el1 er1).
  Proof.
    split; intros. {
      do 2 rewrite by_μe_eq_μEntropy_op.

      apply (coarsening (A_rel ℝ)); [apply H; tauto |].
      intros B vl0 vl1 Hvl.
      unfold preimage.
      f_equal.

      apply (coarsening (A_rel ℝ)); [apply H0; tauto |].
      intros B0 vr0 vr1 Hvr.
      unfold preimage.
      f_equal.

      destruct_val vl0.
      destruct_val vl1.
      destruct_val vr0.
      destruct_val vr1.

      hnf in Hvl, Hvr.
      d_destruct (Hvl, Hvr).
      unfold op_in; simpl.

      unfold indicator.
      f_equal.
      apply HA.
      reflexivity.
    } {
      subst.
      d_destruct Hτ.
      subst e0' e1'.
      cbn.

      rewrite 2 obs_help_op.

      apply (coarsening (A_rel _)); [apply H; tauto |].
      intros B vl0 vl1 Hvl.
      unfold preimage.
      f_equal.

      destruct_val vl0.
      destruct_val vl1.
      inject Hvl.

      destruct H0 as [_ ?].
      specialize (H0 eq_refl eq_refl).
      cbn in H0.

      destruct_val v.
      unfold obs_op_in, ">>="; cbn.
      destruct δ_unique_inv; auto.
      unfold ennr_div.
      rewrite <- 2 integration_linear_mult_r.
      f_equal.
      apply H0.
    }
  Qed.

  Lemma by_μe_eq_μEntropy_hide (e : expr · ℝ ObsR) :
    μ (e_hide_observable e) =
    μ e >>= dirac.
  Proof.
    extensionality A.

    rewrite μe_eq_μEntropy.

    integrand_extensionality σ.
    unfold eval_in.

    decide_eval (e_hide_observable e) σ as [v w ex u]; simpl. {
      d_destruct ex; try absurd_val.

      decide_eval as [ve we exe ue].
      cbn.
      destruct (ue _ _ ex); subst.
      reflexivity.
    } {
      decide_eval as [ve we exe ue].
      econtradict not_ex.
    }
  Qed.

  Lemma μ_hide e : μ (e_hide_observable e) = μ e.
  Proof.
    extensionality A.
    integrand_extensionality σ.
    unfold eval_in.
    decide_eval e σ as [v w E u];
      decide_eval as [v' w' E' u'].
    {
      cbn.
      specialize (u' _ _ (EHide _ E)).
      inject u'.
      auto.
    } {
      d_destruct E'; try absurd_val.
      econtradict not_ex.
    }
  Qed.

  Lemma case_hide : forall e0 e1,
      E_rel ℝ ObsR e0 e1 ->
      E_rel ℝ ObsNone (e_hide_observable e0) (e_hide_observable e1).
  Proof.
    split; [| discriminate]; intros.

    rewrite 2 μ_hide.
    apply H; auto.
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

    pose proof fundamental_property body as fp.
    specialize (fp _ _ (G_rel_cons H G_rel_nil)).

    elim_sig_exprs.
    elim_erase_eqs.

    apply fp; auto.
  }
Qed.

Lemma μ_of_obs_μ e v A :
  obs_μ e v A = indicator A tt * μ (e_observe v e) full_event.
Proof.
  rewrite by_μe_eq_μEntropy_observe.
  rewrite val_is_dirac.
  rewrite meas_id_left.

  setoid_rewrite <- integration_linear_mult_l.
  cbn.
  ring.
Qed.
