(** printing μ_e #μ<sub>e</sub># *)

Require Import Coq.Reals.Reals.
Require Import Coq.Relations.Relations.

Require Import utils.
Require Import syntax.
Require Import integration.

Require determinism.
Import determinism.eval_dec.

Local Open Scope ennr.

(** * The value measure [μ_e] *)

(** We make use of [eval_dec] to define evaluation as [ev], a partial function
    of values, and [ew] a total function for weights. *)
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

(** [eval_in] is the value measure of an expression at exactly one entropy. It
    concentrates all weight on at most one value. *)
Definition eval_in {τ} (e : expr · τ) σ : Meas (val τ) :=
  fun A =>
    option0 (indicator A <$> ev e σ) * ew e σ.

(** [μ] is the value measure of an expression across all entropies. It will be
    the basis for our notion of equivalence. *)
Definition μ {τ} (e : expr · τ) : Meas (val τ) :=
  μEntropy >>= eval_in e.

(** * The logical relation *)

(** We now begin defining our logical relation for contextual equivalence. Since
    the relations are mutually recursive, we have to be somewhat careful in how
    we tie the recursive knot to appease the termination/positivity checkers.
    This is done by defining [A_rel'] and [E_rel'] that take as a parameter the
    V relation at a specific type. Once [V_rel] is defined using [A_rel'] we can
    close [A_rel] with it. *)

(** ---- *)

(** Two events are A-related if they agree on all V-related values. *)
Definition A_rel' (τ : Ty) (V_rel_τ : relation (val τ)) : relation (Event (val τ)) :=
  fun A0 A1 =>
    forall v0 v1 (Hv : V_rel_τ v0 v1),
      (A0 v0 = (* iff *) A1 v1).

(** Two closed expressions are E-related if their value measures agree for all
    A-related events. *)
Definition E_rel' (τ : Ty) (V_rel_τ : relation (val τ)) : relation (expr · τ) :=
  fun e0 e1 =>
    forall A0 A1 (HA : A_rel' τ V_rel_τ A0 A1),
      μ e0 A0 = μ e1 A1.

(** Values at base type are V-related exactly when they are identical *)
Definition V_rel_real : relation (val ℝ) := eq.

(** Values at arrow type are V-related when they take V-related inputs to
    E-related outputs. *)
Inductive V_rel_arrow τa τr
          (V_rel_a : relation (val τa))
          (V_rel_r : relation (val τr))
  : relation (val (τa ~> τr)) :=
| mk_V_rel_arrow (body0 body1 : expr (τa :: ·) τr) :
    (forall (va0 va1 : val τa),
        V_rel_a va0 va1 ->
        E_rel' τr V_rel_r
               (proj1_sig (ty_subst1 body0 va0))
               (proj1_sig (ty_subst1 body1 va1))) ->
      V_rel_arrow τa τr V_rel_a V_rel_r
                  (v_lam body0)
                  (v_lam body1).
Arguments mk_V_rel_arrow {_ _ _ _ _ _} Hva.

(** [V_rel] can't be defined as an inductive without angering the positivity
    checker. Instead, it is defined in pieces by type, then assembled by
    fixpoint. *)
Fixpoint V_rel τ : relation (val τ) :=
  match τ with
  | ℝ => V_rel_real
  | τa ~> τr => V_rel_arrow τa τr (V_rel τa) (V_rel τr)
  end.

Definition A_rel τ := A_rel' τ (V_rel τ).
Definition E_rel τ := E_rel' τ (V_rel τ).

(** Two value environments are G-related when they agree on domain and all their
    values are V-related. *)
Inductive G_rel : forall Γ, relation (wt_env Γ) :=
| G_rel_nil : G_rel · dep_nil dep_nil
| G_rel_cons {τ Γ v0 v1 ρ0 ρ1} :
    V_rel τ v0 v1 -> G_rel Γ ρ0 ρ1 ->
    G_rel (τ :: Γ) (dep_cons v0 ρ0) (dep_cons v1 ρ1).

(** Two open expressions are related when they are E-related after being closed
    by G-related environments. *)
Definition related_exprs Γ τ : relation (expr Γ τ) :=
  fun e0 e1 =>
    forall ρ0 ρ1 (Hρ : G_rel Γ ρ0 ρ1),
      E_rel τ (proj1_sig (close ρ0 e0)) (proj1_sig (close ρ1 e1)).

Notation "'EXP' Γ ⊢ e0 ≈ e1 : τ" :=
  (related_exprs Γ τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, no associativity).

(** Our goal will be to prove that related_exprs is reflexive, but we will need
    some lemmas first. *)

(** * Tactics *)

Ltac fold_μ :=
  match goal with
  | [ |- context [ μEntropy >>= eval_in ?e ] ] => fold (μ e)
  | [ H : context [ μEntropy >>= eval_in ?e ] |- _ ] => fold (μ e)
  end.

(** [decide_eval e, σ as [v, w, E, u]] is a tactic to perform case analysis on
    the partiality of evaluation, and to get rid of [ev e σ] and [ew e σ]. It
    also does other stuff that tries to automatically solve the no-evaluation
    case. It binds the value and weight of the result to [v] and [w], the
    evaluation tree to [E], and the proof that [(v, w)] is unique to u. *)
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
               | Finite
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

(** * Lemmas *)

(** If we can rewrite a measure into a dirac, we can often remove an integral
    through the monad laws. The value measure of a value is such a hidden dirac.
    *)
Lemma val_is_dirac {τ} (v : val τ) :
  μ v = dirac v.
Proof.
  extensionality A.
  unfold μ, dirac.
  apply integration_const_entropy; intro σ.
  unfold eval_in.

  decide_eval as [v' w E u]; cbn.
  destruct (invert_eval_val E).
  subst.
  ring.
Qed.

(** A helper to look up a V-relation from a G-relation  *)
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
    dep_destruct (ρ0, ρ1, H1, H2).
    dep_destruct H.

    cbn in *.
    elim_erase_eqs.
    apply val_eq in x0.
    apply val_eq in x.
    subst.
    auto.
  } {
    dep_destruct (Γ, H0).
    dep_destruct (ρ0, ρ1, H1, H2).
    dep_destruct H.
    eapply IHx; eauto.
  }
Qed.

(** A helper lemma and tactic for applying the coarsening lemma *)
Lemma coarsen_helper {τ X} (e0 e1 : expr · τ) (f0 f1 : val τ -> Meas X) (A0 A1 : Event X) :
  E_rel τ e0 e1 ->
  (forall v0 v1, V_rel τ v0 v1 -> f0 v0 A0 = f1 v1 A1) ->
  (μ e0 >>= f0) A0 = (μ e1 >>= f1) A1.
Proof.
  intros.
  apply (coarsening (A_rel τ)); auto.

  intros B v0 v1 Hv.
  cbn.
  f_equal.
  apply H0.
  apply Hv.
Qed.

Ltac coarsen v :=
  let v0 := fresh v in
  let v1 := fresh v in
  let Hv := fresh "H" v in
  apply coarsen_helper; [tauto |]; intros v0 v1 Hv.

(** It is convenient to be able to talk about the evaluation of an expression as
    transformer of value measures. We will prove they correspond to the value
    measure of the whole expression later in [plus_as_transformer] and similar. *)
Definition plus_in (v v' : val ℝ) : Meas (val ℝ) :=
    match (v : expr · ℝ), (v' : expr · ℝ) with
    | e_real r, e_real r' => fun A => indicator A (v_real (r + r'))
    | _, _ => (* never happens *) empty_meas _
    end.

Definition factor_in (v : val ℝ) : Meas (val ℝ) :=
  match (v : expr · ℝ) with
  | e_real r =>
    match Rle_dec 0 r with
    | left rpos => unif_score_meas (finite r rpos) (dirac (v_real r))
    | _ => empty_meas _
    end
  | _ => (* never happens *) empty_meas _
  end.

Definition apply_in {τa τr} (vf : val (τa ~> τr)) (va : val τa) :
  Entropy -> Meas (val τr) :=
  match (vf : expr _ _) in (expr _ τ)
        return (τ = τa ~> τr -> Entropy -> Meas (val τr))
  with
  | e_lam body => fun H => ltac:(inject H; refine (eval_in (proj1_sig (ty_subst1 body va))))
  | _ => (* never happens *) fun _ _ => empty_meas _
  end eq_refl.

(** (Theorem 7) [μe_eq_μEntropy] changes an integral over a program measure into
    an integral over entropy. This is useful since we know a lot more about
    integrating by entropies than by programs. We will use it in
    [plus_as_val_transformer] and the others like it. *)
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

  destruct (ev _ _); cbn. {
    setoid_rewrite integration_of_indicator.
    rewrite lebesgue_pos_measure_interval.
    reflexivity.
  } {
    apply integration_of_0.
  }
Qed.

(* [μe_eq_μEntropy2] is the two argument version of [μe_eq_μEntropy]. It's
   better than just using the original twice because it moves all the option
   machinery into the very inside. *)
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

  decide_eval as [v w E u]; cbn; auto.
  rewrite <- integration_linear_mult_l.
  ring.
Qed.

Lemma plus_as_transformer (el er : expr · ℝ) :
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
      dep_destruct (H, H1).

      cbn.
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


Lemma apply_as_transformer {τa τr}
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
      dep_destruct exr; try absurd_val.
      rename va into va'.
      decide_eval ef (π 0 σ) as [vf wf exf uf].
      decide_eval ea (π 1 σ) as [va wa exa ua].
      simpl.

      destruct_val vf.
      cbn.

      destruct (uf _ _ exr1), (ua _ _ exr2); subst.
      dep_destruct H.

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
      cbn.

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

    decide_eval ef σf as [vf wf exf uf]; [| apply integration_of_0].
    decide_eval ea σa as [va wa exa ua]; [| apply integration_of_0].
    cbn.
    reflexivity.
  }
Qed.

Lemma factor_as_transformer (e : expr · ℝ) :
  μ (e_factor e) =
  μ e >>= factor_in.
Proof.
  extensionality A.

  rewrite μe_eq_μEntropy.

  integrand_extensionality σ.
  unfold eval_in.

  decide_eval (e_factor e) σ as [vr wr exr ur]; simpl. {
    destruct_val vr.
    dep_destruct exr; try absurd_val.

    decide_eval as [ve we exe ue].
    destruct (ue _ _ exr); subst.

    cbn.
    destruct Rle_dec; [| contradiction].
    replace (finite r r0) with (finite r rpos) by Finite.
    cbn.
    ring.
  } {
    decide_eval as [ve we exe ue].
    destruct_val ve.
    cbn.

    destruct Rle_dec; cbn; try ring.
    specialize (not_ex (v_real r) (finite r r0 * we)).
    econtradict not_ex.
  }
Qed.

(** ** Compatibility Lemmas *)

Lemma compat_real Γ r :
  (EXP Γ ⊢ e_real r ≈ e_real r : ℝ).
Proof.
  repeat intro.
  elim_sig_exprs.
  elim_erase_eqs.

  rewrite rewrite_v_real.
  rewrite val_is_dirac.
  unfold dirac, indicator.
  f_equal.
  apply HA.

  hnf.
  reflexivity.
Qed.

Lemma compat_var Γ x τ
      (Hx : lookup Γ x = Some τ) :
  EXP Γ ⊢ e_var x Hx ≈ e_var x Hx : τ.
Proof.
  repeat intro.
  elim_sig_exprs.

  destruct (env_search_subst ρ0 Hx) as [v0 ρ0x].
  destruct (env_search_subst ρ1 Hx) as [v1 ρ1x].

  pose proof (apply_G_rel Hρ Hx ρ0x ρ1x).
  elim_erase_eqs.

  rewrite 2 val_is_dirac.
  unfold dirac, indicator.
  f_equal.
  exact (HA _ _ H).
Qed.

Lemma compat_lam Γ τa τr body0 body1 :
  (EXP (τa :: Γ) ⊢ body0 ≈ body1 : τr) ->
  (EXP Γ ⊢ e_lam body0 ≈ e_lam body1 : (τa ~> τr)).
Proof.
  repeat intro.
  elim_sig_exprs.
  elim_erase_eqs.

  rewrite 2 rewrite_v_lam.
  rewrite 2 val_is_dirac.

  unfold dirac, indicator.
  f_equal.
  apply HA.

  constructor.
  intros.

  specialize (H (dep_cons va0 ρ0) (dep_cons va1 ρ1) (G_rel_cons H0 Hρ)).

  elim_sig_exprs.
  elim_erase_eqs.
  asimpl in He3.
  asimpl in He4.
  elim_erase_eqs.

  apply H.
Qed.

Lemma compat_plus Γ el0 er0 el1 er1 :
  (EXP Γ ⊢ el0 ≈ el1 : ℝ) ->
  (EXP Γ ⊢ er0 ≈ er1 : ℝ) ->
  (EXP Γ ⊢ e_plus el0 er0 ≈ e_plus el1 er1 : ℝ).
Proof.
  intros Hl Hr.

  repeat intro.

  specialize (Hl _ _ Hρ).
  specialize (Hr _ _ Hρ).

  elim_sig_exprs.
  dep_destruct (e3, He3).
  dep_destruct (e4, He4).
  elim_erase_eqs.

  clear el0 el1 er0 er1 He He0 He1 He2.

  do 2 rewrite plus_as_transformer.

  coarsen vl.
  coarsen vr.

  destruct_val vl.
  destruct_val vl0.
  destruct_val vr.
  destruct_val vr0.

  inject Hvl.
  inject Hvr.

  cbn.
  unfold indicator.
  erewrite HA; eauto.
  reflexivity.
Qed.

Lemma compat_app Γ τa τr ef0 ef1 ea0 ea1 :
  (EXP Γ ⊢ ef0 ≈ ef1 : (τa ~> τr)) ->
  (EXP Γ ⊢ ea0 ≈ ea1 : τa) ->
  (EXP Γ ⊢ e_app ef0 ea0 ≈ e_app ef1 ea1 : τr).
Proof.
  intros Hf Ha.

  repeat intro.

  specialize (Hf _ _ Hρ).
  specialize (Ha _ _ Hρ).

  elim_sig_exprs.
  elim_erase_eqs.

  clear ef0 ef1 ea0 ea1 He He0 He1 He2.

  do 2 rewrite apply_as_transformer.

  coarsen vf.
  coarsen va.

  destruct Hvf as [? ? Hvf].
  cbn; repeat fold_μ.
  apply Hvf; auto.
Qed.

Lemma compat_sample Γ :
  EXP Γ ⊢ e_sample ≈ e_sample : ℝ.
Proof.
  repeat intro.

  elim_sig_exprs.
  elim_erase_eqs.

  f_equal.
  extensionality v.

  apply HA.
  reflexivity.
Qed.

Lemma compat_factor Γ e0 e1:
  (EXP Γ ⊢ e0 ≈ e1 : ℝ) ->
  (EXP Γ ⊢ e_factor e0 ≈ e_factor e1 : ℝ).
Proof.
  repeat intro.

  specialize (H _ _ Hρ).

  elim_sig_exprs.
  elim_erase_eqs.

  clear e0 e1 He He2.

  rewrite 2 factor_as_transformer.

  coarsen v.

  destruct Hv.
  destruct_val v.

  cbn.
  destruct Rle_dec; auto.

  cbn.
  unfold indicator.
  do 2 f_equal.
  apply HA.
  reflexivity.
Qed.

(** * The fundamental property *)
Lemma fundamental_property {Γ τ} (e : expr Γ τ) :
  (EXP Γ ⊢ e ≈ e : τ).
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