(** printing μ_e #μ<sub>e</sub># *)

Require Import Coq.Reals.Reals.
Require Import Coq.Relations.Relations.

Require Import utils.
Require Import syntax.
Require Import integration.
Require Import logrel.
Require Import determinism.

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

Import Log_rel2.
Module CtxEquivBase <: BASE.

  (** Values at base type are V-related exactly when they are identical *)
  Definition V_rel_real : rel (val ℝ) := eq.

(** Two events are A-related if they agree on all V-related values. *)
  Definition A_rel' (τ : Ty) (V_rel_τ : rel (val τ)) : rel (Event (val τ)) :=
    fun A0 A1 =>
      forall v0 v1 (Hv : V_rel_τ v0 v1),
        (A0 v0 = (* iff *) A1 v1).

  (** Two closed expressions are E-related if their value measures agree for all
      A-related events. *)
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
    let v0 := fresh v "0" in
    let v1 := fresh v "1" in
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
  Arguments plus_in !_ !_.

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

    setoid_rewrite meas_bind_assoc.
    integrand_extensionality σ.

    unfold eval_in.
    setoid_rewrite ennr_mul_comm.
    rewrite integration_linear_in_meas.
    f_equal.

    destruct ev; cbn. {
      fold (dirac v).
      rewrite meas_id_left.
      reflexivity.
    } {
      fold (empty_meas (val τ)).
      rewrite bind_empty.
      reflexivity.
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
    setoid_rewrite μe_eq_μEntropy.
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
      dep_destruct H.

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

  Lemma case_app : forall τa τr ef0 ef1 ea0 ea1,
      E_rel (τa ~> τr) ef0 ef1 ->
      E_rel τa ea0 ea1 ->
      E_rel τr (e_app ef0 ea0) (e_app ef1 ea1).
  Proof.
    repeat intro.
    rewrite 2 apply_as_transformer.

    coarsen vf.
    coarsen va.

    destruct Hvf as [? ? Hvf].
    cbn.
    repeat fold_μ.

    apply Hvf; auto.
  Qed.

  Lemma case_factor : forall e0 e1,
      E_rel ℝ e0 e1 ->
      E_rel ℝ (e_factor e0) (e_factor e1).
  Proof.
    repeat intro.
    rewrite 2 factor_as_transformer.

    coarsen v.
    destruct Hv.
    destruct_val v0.

    cbn.
    destruct Rle_dec; auto.

    cbn.
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

  Lemma case_plus : forall el0 el1 er0 er1,
      E_rel ℝ el0 el1 ->
      E_rel ℝ er0 er1 ->
      E_rel ℝ (e_plus el0 er0) (e_plus el1 er1).
  Proof.
    repeat intro.

    rewrite 2 plus_as_transformer.

    coarsen vl.
    coarsen vr.
    destruct Hvl.
    destruct_val vl0.
    destruct Hvr.
    destruct_val vr0.

    cbn.
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

    pose proof fundamental_property body as fp.
    specialize (fp _ _ (G_rel_cons H G_rel_nil)).

    elim_sig_exprs.
    elim_erase_eqs.

    apply fp; auto.
  }
Qed.
