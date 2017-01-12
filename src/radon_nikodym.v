Require Import Basics.
Require Import Reals.
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
Require Import ctxequiv.
Require Import properties_of_relations.

Definition is_RN_deriv {X} (ν : Meas X) (μ : Meas X) (f : X -> R+) : Prop :=
  forall A,
    ν A = integration (fun x => indicator A x * f x) μ.

Axiom lebesgue_measure : Meas R.

Definition lebesgue_val_measure : Meas (val ℝ) :=
 fun A => lebesgue_measure (fun r => A (v_real r)).


Goal forall e,
    is_RN_deriv (μ e) lebesgue_val_measure (fun v => obs_μ e v full_event).
  unfold is_RN_deriv.
  intros.
  unfold obs_μ.
  cbn.
  setoid_rewrite ennr_mul_1_l.
Abort.


Require Import logrel.
Import Log_rel1_prop.
Module RadonNikodymBase <: BASE.
  Definition V_rel_real : rel (val ℝ) := fun _ => True.

  Inductive E_rel'' : forall (τ : Ty) (ϕ : Effect) (v_rel_τ : rel (val τ)), rel (expr · τ ϕ) :=
  | E_rel'_obsR (v_rel_τ : rel (val ℝ)) e :
      is_RN_deriv (μ e) lebesgue_val_measure (fun v => obs_μ e v full_event) ->
      @E_rel'' ℝ ObsR v_rel_τ e
  | E_rel'_obsNone τ (v_rel_τ : rel (val τ)) e :
      @E_rel'' τ ObsNone v_rel_τ e.

  (* Coq can't handle inductive parameters, so add an extra bit of indirection *)
  Definition E_rel' τ ϕ (v_rel_τ : rel (val τ)) e :=
    (forall σ v w, (EVAL σ ⊢ e ⇓ v, w) -> v_rel_τ v) /\
    forall (Hτ : τ = ℝ)
           (Hϕ : ϕ = ObsR),
      let e' := (rew [fun ϕ => expr · ℝ ϕ] Hϕ in
                    rew [fun τ => expr · τ ϕ] Hτ in
                    e) in
      is_RN_deriv (μ e') lebesgue_val_measure (fun v => obs_μ e' v full_event).
End RadonNikodymBase.

Module RadonNikodymCases : CASES RadonNikodymBase.
  Module Defs := Defs RadonNikodymBase.
  Export Defs.

  Lemma case_val : forall τ v,
      V_rel τ v -> E_rel τ _ v.
  Proof.
    intros.
    split; [| discriminate]; intros.
    destruct (invert_eval_val H0); subst.
    auto.
  Qed.

  Lemma case_real : forall r,
      E_rel ℝ _ (e_real r).
  Proof.
    split; [| discriminate]; intros.
    constructor.
  Qed.

  Lemma case_lam : forall τa ϕ τr body,
      (forall v,
          V_rel τa v ->
          E_rel τr _ (proj1_sig (ty_subst1 body v))) ->
      E_rel (τa ~~ ϕ ~> τr) _ (e_lam body).
  Proof.
    split; [| discriminate]; intros.

    rewrite rewrite_v_lam in H0.
    destruct (invert_eval_val H0); subst.
    constructor; intros.
    apply H; auto.
  Qed.

  Lemma case_app : forall τa ϕ τr ϕf ϕa ef ea,
      E_rel (τa ~~ ϕ ~> τr) ϕf ef ->
      E_rel τa ϕa ea ->
      E_rel τr _ (e_app ef ea).
  Proof.
    split; intros. {
      intros.
      d_destruct H1; try absurd_val.

      destruct H as [H _], H0 as [H0 _].
      specialize (H (π 0 σ) _ _ H1_).
      specialize (H0 (π 1 σ) _ _ H1_0).

      cbn in H.
      d_destruct H.
      specialize (H va H0).

      destruct H as [H _].
      eapply H; eauto.
    } {
      subst.
      subst e'.
      cbn.

      unfold is_RN_deriv.
      intros.
      rewrite by_μe_eq_μEntropy_app.
      admit.
    }
  Admitted.

  Lemma case_factor : forall ϕ e,
      E_rel ℝ ϕ e ->
      E_rel ℝ _ (e_factor e).
  Proof.
  Admitted.

  Definition lebesgue_01_ivl : Meas (val ℝ) :=
    fun A => lebesgue_measure (fun r =>
                                 if Rle_dec 0 r
                                 then if Rle_dec r 1
                                      then A (v_real r)
                                      else false
                                 else false).

  Lemma meas_of_sample :
    μ e_sample = lebesgue_01_ivl.
  Proof.
    extensionality A.
  Qed.

  Lemma case_sample :
    E_rel ℝ _ e_sample.
  Proof.
    split; intros. {
      d_destruct H; try absurd_val.
      constructor.
    } {
      d_destruct (Hτ, Hϕ).
      subst e'.
      cbn.

      intro.

      replace (μ e_sample A)
    }
  Qed.

  Lemma case_observe : forall ϕ0 e0 e1,
      E_rel ℝ ϕ0 e0 ->
      E_rel ℝ _ e1 ->
      E_rel ℝ _ (e_observe e0 e1).
  Proof.
  Qed.

  Lemma case_binop : forall ϕl ϕr op el er,
      E_rel ℝ ϕl el ->
      E_rel ℝ ϕr er ->
      E_rel ℝ _ (e_binop op el er).
  Proof.
  Qed.

  Lemma case_hide : forall e,
      E_rel ℝ ObsR e ->
      E_rel ℝ ObsNone (e_hide_observable e).
  Proof.
  Qed.
  .

End RadonNikodymCases.



Lemma radon_nikodym (e : expr · ℝ ObsR) :
  is_RN_deriv (μ e) lebesgue_val_measure (fun v => obs_μ e v full_event).
Proof.
Qed.