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
Require determinism.
Import determinism.eval_dec.

Local Open Scope ennr.

Definition Event X := X -> bool.

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

(* ifte is a function version of "if then else" so that f_equal can deal with it *)
Definition ifte {X} (a : bool) (b c : X) := if a then b else c.
Definition indicator {X} (b : Event X) : X -> R+ := fun x => ifte (b x) 1 0.

Definition Meas A := (Event A -> R+).

Definition eval_in {τ} (e : expr · τ) σ : Meas (val τ) :=
  fun A =>
    option0 (indicator A <$> ev e σ) * ew e σ.

Axiom μEntropy : Meas Entropy.

Axiom integration : forall {A}, (A -> R+) -> Meas A -> R+.

(* show (∫ f dμ = ∫ g dμ) by showing pointwise equality *)
Ltac integrand_extensionality x :=
  refine (f_equal2 integration _ eq_refl); extensionality x.

Axiom integration_linear :
  forall {A} (μ : Meas A) (s0 s1 : R+) (f0 f1 : A -> R+),
    s0 * integration f0 μ + s1 * integration f1 μ =
    integration (fun x => s0 * f0 x + s1 * f1 x) μ.

Lemma integration_linear_mult_r :
  forall {A} (μ : Meas A) (s : R+) (f : A -> R+),
    integration f μ * s =
    integration (fun x => f x * s) μ.
Proof.
  intros.

  replace (integration f μ * s)
  with (s * integration f μ + 0 * integration f μ)
    by ring.

  rewrite integration_linear.
  integrand_extensionality x.
  ring.
Qed.

Lemma integration_linear_mult_l :
  forall {A} (μ : Meas A) (s : R+) (f : A -> R+),
    s * integration f μ =
    integration (fun x => s * f x) μ.
Proof.
  intros.
  rewrite ennr_mul_comm.
  rewrite integration_linear_mult_r.
  integrand_extensionality x.
  ring.
Qed.

Definition bool_of_dec {A B} : sumbool A B -> bool :=
  fun x => if x then true else false.

Axiom lebesgue_pos_measure : Meas R+.
Axiom lebesgue_pos_measure_interval :
  forall (r : R+),
    lebesgue_pos_measure (fun x => bool_of_dec (r [>] x)) = r.

Axiom riemann_def_of_lebesgue_integration :
  forall {A} μ (f : A -> R+),
    integration f μ =
    integration
      (fun t => μ (fun x => bool_of_dec (f x [>] t)))
      lebesgue_pos_measure.

Axiom integration_of_indicator :
  forall {A}
         (m : Meas A)
         (f : Event A),
    integration (fun x => indicator f x) m = m f.

Definition meas_bind {A B} (μ : Meas A) (f : A -> Meas B) : Meas B :=
  fun ev => integration (fun a => f a ev) μ.
Infix ">>=" := meas_bind (at level 20).

Definition fold_bind {A B} (μ : Meas A) (f : A -> Meas B) V :
  integration (fun a => f a V) μ = (μ >>= f) V := eq_refl.

Definition dirac {A} (v : A) : Meas A :=
  fun e => indicator e v.

Lemma meas_id_left {A B} b (f : A -> Meas B) :
  dirac b >>= f = f b.
Proof.
  extensionality ev.
  unfold ">>=".
  unfold dirac.
  rewrite riemann_def_of_lebesgue_integration.
  setoid_rewrite integration_of_indicator.
  apply lebesgue_pos_measure_interval.
Qed.

Lemma meas_id_right {A} (μ : Meas A) :
  μ >>= dirac = μ.
Proof.
  extensionality ev.
  apply integration_of_indicator.
Qed.

Lemma meas_bind_assoc {A B C} (μ : Meas A) (f : A -> Meas B) (g : B -> Meas C) :
  (μ >>= f) >>= g = μ >>= (fun x => f x >>= g).
Proof.
Admitted.

Definition μ {τ} (e : expr · τ) : Meas (val τ) :=
  μEntropy >>= eval_in e.

Ltac fold_μ :=
  match goal with
  | [ |- context [ μEntropy >>= eval_in ?e ] ] => fold (μ e)
  | [ H : context [ μEntropy >>= eval_in ?e ] |- _ ] => fold (μ e)
  end.

Definition A_rel' (τ : Ty) (V_rel_τ : relation (val τ)) : relation (Event (val τ)) :=
  fun A0 A1 =>
    forall v0 v1 (Hv : V_rel_τ v0 v1),
      (A0 v0 = (* iff *) A1 v1).

Definition E_rel' (τ : Ty) (V_rel_τ : relation (val τ)) : relation (expr · τ) :=
  fun e0 e1 =>
    forall A0 A1 (HA : A_rel' τ V_rel_τ A0 A1),
      μ e0 A0 = μ e1 A1.

Definition V_rel_real : relation (val ℝ) := eq.

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

Fixpoint V_rel τ : relation (val τ) :=
  match τ with
  | ℝ => V_rel_real
  | τa ~> τr => V_rel_arrow τa τr (V_rel τa) (V_rel τr)
  end.

Definition A_rel τ := A_rel' τ (V_rel τ).
Definition E_rel τ := E_rel' τ (V_rel τ).

Inductive G_rel : forall Γ, relation (wt_env Γ) :=
| G_rel_nil : G_rel · dep_nil dep_nil
| G_rel_cons {τ Γ v0 v1 ρ0 ρ1} :
    V_rel τ v0 v1 -> G_rel Γ ρ0 ρ1 ->
    G_rel (τ :: Γ) (dep_cons v0 ρ0) (dep_cons v1 ρ1).

Lemma apply_G_rel {Γ ρ0 ρ1} :
  G_rel Γ ρ0 ρ1 ->
  forall {x τ} {v0 v1 : val τ},
    lookup Γ x = Some τ ->
    dep_lookup ρ0 x = Some (existT _ τ v0) ->
    dep_lookup ρ1 x = Some (existT _ τ v1) ->
    V_rel τ v0 v1.
Proof.
  intros.
  revert Γ ρ0 ρ1 H H0 H1 H2.
  induction x; intros. {
    d_destruct (Γ, H0).
    d_destruct (ρ0, ρ1, H1, H2).
    d_destruct H.
    auto.
  } {
    d_destruct (Γ, H0).
    d_destruct (ρ0, ρ1, H1, H2).
    d_destruct H.
    eapply IHx; eauto.
  }
Qed.

Definition related_exprs Γ τ : relation (expr Γ τ) :=
  fun e0 e1 =>
    forall ρ0 ρ1 (Hρ : G_rel Γ ρ0 ρ1),
      E_rel τ (proj1_sig (close ρ0 e0)) (proj1_sig (close ρ1 e1)).

Notation "'EXP' Γ ⊢ e0 ≈ e1 : τ" :=
  (related_exprs Γ τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, no associativity).

Ltac econtradict e := exfalso; eapply e; repeat econstructor; eauto.

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

Ltac what_equality_am_I_proving :=
  match goal with
  | [ |- @eq ?t ?l ?r ] => idtac "proving" l "=" r "at type" t
  | _ => idtac "it doesn't look like your goal is an equality"
  end.

(* TODO: rewrite as μEntropy(True) = 1 and linearity *)
Axiom int_const_entropy :
  forall (v : R+)
         (f : Entropy -> R+),
    (forall x, f x = v) ->
    integration f μEntropy = v.

Lemma is_val_of_is_pure {τ} (e : expr · τ) :
  is_pure e ->
  is_val e.
Proof.
  intros.
  destruct e; try contradiction H; trivial.
  discriminate H0.
Qed.

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

Lemma lam_is_dirac {τa τ} (e : expr (τa :: ·) τ) :
  μ (e_lam e) = dirac (v_lam e).
Proof.
  rewrite <- val_is_dirac.
  auto.
Qed.

Lemma compat_real Γ r :
  (EXP Γ ⊢ e_real r ≈ e_real r : ℝ).
Proof.
  repeat intro.
  elim_sig_exprs.
  d_destruct (e, He).
  d_destruct (e0, He0).

  change (μ (v_real r) A0 = μ (v_real r) A1).
  rewrite val_is_dirac.
  unfold dirac, indicator; simpl.
  f_equal.
  apply HA.
  reflexivity.
Qed.

Lemma compat_var Γ x τ
      (Hx : lookup Γ x = Some τ) :
  EXP Γ ⊢ e_var x Hx ≈ e_var x Hx : τ.
Proof.
  repeat intro.
  elim_sig_exprs.

  destruct (env_search ρ0 Hx) as [v0 ρ0x].
  destruct (env_search ρ1 Hx) as [v1 ρ1x].

  pose proof (apply_G_rel Hρ Hx ρ0x ρ1x).

  apply lookup_subst in ρ0x.
  apply lookup_subst in ρ1x.
  elim_erase_eqs.

  rewrite 2 val_is_dirac.
  unfold dirac, indicator.
  f_equal.
  apply HA.
  auto.
Qed.

Lemma compat_lam Γ τa τr body0 body1 :
  (EXP (τa :: Γ) ⊢ body0 ≈ body1 : τr) ->
  (EXP Γ ⊢ e_lam body0 ≈ e_lam body1 : (τa ~> τr)).
Proof.
  repeat intro.
  elim_sig_exprs.
  d_destruct (e, He).
  d_destruct (e0, He0).

  rewrite 2 lam_is_dirac.

  unfold dirac, indicator; simpl.
  f_equal.
  apply HA.

  constructor.
  intros.

  specialize (H (dep_cons va0 ρ0) (dep_cons va1 ρ1) (G_rel_cons H0 Hρ)).

  elim_sig_exprs.
  rewrite x0 in He3.
  rewrite x in He4.
  asimpl in He3.
  asimpl in He4.

  elim_erase_eqs.

  apply H.
Qed.

Inductive SigmaFinite : forall {A}, Meas A -> Prop :=
| ent_finite : SigmaFinite μEntropy
| leb_finite : SigmaFinite lebesgue_pos_measure.
Hint Constructors SigmaFinite.

Lemma tonelli_sigma_finite :
  forall {A B} (f : A -> B -> R+) (μx : Meas A) (μy : Meas B),
    SigmaFinite μx ->
    SigmaFinite μy ->
    integration (fun x => integration (fun y => f x y) μy) μx =
    integration (fun y => integration (fun x => f x y) μx) μy.
Admitted.

Definition preimage {A B C} (f : A -> B) : (B -> C) -> (A -> C) :=
  fun eb a => eb (f a).

(* Lemma 3 *)
Lemma coarsening :
  forall {X}
         (M : relation (Event X))
         (μ0 μ1 : Meas X)
         (f0 f1 : X -> R+)
         (μs_agree : forall A0 A1, M A0 A1 -> μ0 A0 = μ1 A1)
         (f_is_M_measurable :
            forall (B : Event R+),
              M (preimage f0 B) (preimage f1 B)),
    integration f0 μ0 = integration f1 μ1.
Proof.
  intros.
  setoid_rewrite riemann_def_of_lebesgue_integration.

  integrand_extensionality t.
  apply μs_agree.

  specialize (f_is_M_measurable (fun fx => bool_of_dec (fx [>] t))).
  unfold preimage in f_is_M_measurable.
  exact f_is_M_measurable.
Qed.

(* Lemma 5 *)
Axiom integration_πL_πR : forall (g : Entropy -> Entropy -> R+),
    integration (fun σ => g (πL σ) (πR σ)) μEntropy =
    integration (fun σL => integration (fun σR => g σL σR) μEntropy) μEntropy.

Lemma bind_πL_πR {B} (g : Entropy -> Entropy -> Meas B) :
  μEntropy >>= (fun σ => g (πL σ) (πR σ)) =
  μEntropy >>= (fun σL => μEntropy >>= (fun σR => g σL σR)).
Proof.
  extensionality ev.
  unfold ">>=".
  rewrite <- integration_πL_πR.
  auto.
Qed.

Lemma pick_3_and_leftover {B}
      (g : Entropy -> Entropy -> Entropy -> Entropy -> Meas B) :
  μEntropy >>= (fun σ => g (π 0 σ) (π 1 σ) (π 2 σ) (π_leftover 3 σ)) =
  μEntropy >>= (fun σ0 =>
  μEntropy >>= (fun σ1 =>
  μEntropy >>= (fun σ2 =>
  μEntropy >>= (fun σR =>
                  g σ0 σ1 σ2 σR)))).
Proof.
  unfold π, π_leftover.

  extensionality A.

  transitivity
    ((μEntropy >>=
               (fun σ0 =>
                  μEntropy >>=
                           (fun σ =>
                              g σ0 (πL σ) (πL (πR σ)) (πR (πR σ))))) A). {
    rewrite <- bind_πL_πR.
    auto.
  }

  integrand_extensionality σ0.
  transitivity
    ((μEntropy >>=
               (fun σ1 =>
                  μEntropy >>=
                           (fun σ => g σ0 σ1 (πL σ) (πR σ)))) A). {
    rewrite <- bind_πL_πR.
      auto.
  }

  integrand_extensionality σ1.
  rewrite <- bind_πL_πR.
  auto.
Qed.

Lemma pick_3_entropies {B}
      (g : Entropy -> Entropy -> Entropy -> Meas B) :
  μEntropy >>= (fun σ => g (π 0 σ) (π 1 σ) (π 2 σ)) =
  μEntropy >>= (fun σ0 =>
  μEntropy >>= (fun σ1 =>
  μEntropy >>= (fun σ2 =>
                  g σ0 σ1 σ2))).
Proof.
  rewrite (pick_3_and_leftover (fun (σ0 σ1 σ2 σR : Entropy) => g σ0 σ1 σ2)).

  extensionality A.

  integrand_extensionality σ0.
  integrand_extensionality σ1.
  integrand_extensionality σ2.
  setoid_rewrite int_const_entropy; auto.
Qed.

Lemma pick_2_entropies {B}
      (g : Entropy -> Entropy -> Meas B) :
  μEntropy >>= (fun σ => g (π 0 σ) (π 1 σ)) =
  μEntropy >>= (fun σ0 =>
  μEntropy >>= (fun σ1 =>
                  g σ0 σ1)).
Proof.
  rewrite (pick_3_entropies (fun (σ0 σ1 σ2 : Entropy) => g σ0 σ1)).

  extensionality A.

  integrand_extensionality σ0.
  integrand_extensionality σ1.
  setoid_rewrite int_const_entropy; auto.
Qed.

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

Lemma work_of_plus
      {el0 er0 el1 er1 : expr · ℝ}
      (Hl : forall Al0 Al1,
          A_rel ℝ Al0 Al1 ->
          μ el0 Al0 = μ el1 Al1)
      (Hr : forall Ar0 Ar1,
          A_rel ℝ Ar0 Ar1 ->
          μ er0 Ar0 = μ er1 Ar1)
      {A0 A1} (HA : A_rel ℝ A0 A1)
  : μ (e_plus el0 er0) A0 = μ (e_plus el1 er1) A1.
Proof.
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
  d_destruct (e3, He3).
  d_destruct (e4, He4).
  elim_erase_eqs.

  apply work_of_plus; auto.
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

Lemma work_of_app {τa τr}
      (ef0 ef1 : expr · (τa ~> τr))
      (ea0 ea1 : expr · τa)
      (Hf : forall Af0 Af1 : Event (val (τa ~> τr)),
          A_rel (τa ~> τr) Af0 Af1 ->
          μ ef0 Af0 = μ ef1 Af1)
      (Ha : forall Aa0 Aa1 : Event (val τa),
          A_rel τa Aa0 Aa1 ->
          μ ea0 Aa0 = μ ea1 Aa1)
      {A0 A1 : Event (val τr)}
      (HA : A_rel τr A0 A1)
  : μ (e_app ef0 ea0) A0 = μ (e_app ef1 ea1) A1.
Proof.
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
  d_destruct (e3, He3).
  d_destruct (e4, He4).
  elim_erase_eqs.

  apply work_of_app; auto.
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

Lemma work_of_factor
  (e0 e1 : expr · ℝ)
  (He : forall A0 A1 : Event (val ℝ),
      A_rel' ℝ (V_rel ℝ) A0 A1 ->
      μ e0 A0 = μ e1 A1)
  (A0 A1 : Event (val ℝ))
  (HA : A_rel' ℝ (V_rel ℝ) A0 A1) :
  μ (e_factor e0) A0 = μ (e_factor e1) A1.
Proof.
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

Lemma compat_factor Γ e0 e1:
  (EXP Γ ⊢ e0 ≈ e1 : ℝ) ->
  (EXP Γ ⊢ e_factor e0 ≈ e_factor e1 : ℝ).
Proof.
  repeat intro.

  specialize (H _ _ Hρ).

  elim_sig_exprs.
  d_destruct (e3, He3).
  d_destruct (e4, He4).
  elim_erase_eqs.

  apply work_of_factor; auto.
Qed.

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
