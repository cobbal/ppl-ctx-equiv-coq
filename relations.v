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
Require determinism.
Import EqNotations.

Local Open Scope R.

Definition Event X := X -> bool.

Definition eval_dec :
  forall {e τ},
    (TC · ⊢ e : τ) ->
    forall σ,
      (existsT! vw : (Val * R+), let (v, w) := vw in EVAL σ ⊢ e ⇓ v, w) +
      ((existsT vw : (Val * R+), let (v, w) := vw in EVAL σ ⊢ e ⇓ v, w) -> False)
  := @determinism.eval_dec.

Definition big_preservation :
  forall {e τ v w σ},
    (TC · ⊢ e : τ) ->
    (EVAL σ ⊢ e ⇓ v, w) ->
    (TC · ⊢ v : τ)
  := @determinism.big_preservation.

Definition ev {e τ} (He : TC · ⊢ e : τ) σ : option (WT_Val τ) :=
  match eval_dec He σ with
  | inl (existT _ (v, w) (evl, _)) =>
    Some (mk_WT_Val _ (big_preservation He evl))
  | inr _ => None
  end.

Definition ew {e τ} (He : TC · ⊢ e : τ) σ : R+ :=
  match eval_dec He σ with
  | inl (existT _ (v, w) _) => w
  | inr _ => nnr_0
  end.

Definition ifte {X} (a : bool) (b c : X) := if a then b else c.
Definition Indicator {X} (b : Event X) : X -> R+ := fun x => ifte (b x) nnr_1 nnr_0.

Definition Meas A := (Event A -> R+).

Definition eval_in {e τ} (He : TC · ⊢ e : τ) σ : Meas (WT_Val τ) :=
  fun A =>
    option0 (Indicator A <$> ev He σ) [*] ew He σ.

Axiom μEntropy : Meas Entropy.

Axiom Integration : forall {A}, (A -> R+) -> Meas A -> R+.
(* Notation "'∫' fx ';' μ ( 'd' x )" := (Integration (fun x => fx) μ). *)

Ltac integrand_extensionality x :=
  refine (f_equal2 Integration _ eq_refl); extensionality x.

Axiom Integration_linear :
  forall {A} (μ : Meas A) (s0 s1 : R+) (f0 f1 : A -> R+),
    s0 [*] Integration f0 μ [+] s1 [*] Integration f1 μ =
    Integration (fun x => s0 [*] f0 x [+] s1 [*] f1 x) μ.

Lemma Integration_linear_mult_r :
  forall {A} (μ : Meas A) (s : R+) (f : A -> R+),
    Integration f μ [*] s =
    Integration (fun x => f x [*] s) μ.
Proof.
  intros.
  nnr.
  simpl.
  rewrite Rmult_comm.
  rewrite <- Rplus_0_r at 1.
  rewrite <- Rmult_0_l with (r := _r (Integration (const nnr_0) μ)).
  replace 0 with (_r nnr_0) by auto.

  replace (_ + _) with
  (_r (s [*] Integration f μ [+] nnr_0 [*] Integration (const nnr_0) μ))
    by auto.
  f_equal.
  rewrite Integration_linear.
  integrand_extensionality x.
  nnr.
Qed.

Lemma Integration_linear_mult_l :
  forall {A} (μ : Meas A) (s : R+) (f : A -> R+),
    s [*] Integration f μ =
    Integration (fun x => s [*] f x) μ.
Proof.
  intros.
  rewrite nnr_mult_comm.
  rewrite Integration_linear_mult_r.
  integrand_extensionality x.
  nnr.
Qed.

Definition bool_of_dec {A B} : sumbool A B -> bool :=
  fun x => if x then true else false.

Axiom lebesgue_measure : Meas R.
Axiom lebesgue_measure_interval :
  forall (r : R+),
    lebesgue_measure (fun x => bool_of_dec (r [>] x)) = r.

Axiom riemann_def_of_lebesgue_integration :
  forall {A} μ (f : A -> R+),
    Integration f μ =
    Integration
      (fun t => μ (fun x => bool_of_dec (f x [>] t)))
      lebesgue_measure.

Axiom integration_of_indicator :
  forall {A}
         (m : Meas A)
         (f : Event A),
    Integration (fun x => Indicator f x) m = m f.

Definition meas_bind {A B} (μ : Meas A) (f : A -> Meas B) : Meas B :=
  fun ev => Integration (fun a => f a ev) μ.
Infix ">>=" := meas_bind (at level 20).

Definition fold_bind {A B} (μ : Meas A) (f : A -> Meas B) V :
  Integration (fun a => f a V) μ = (μ >>= f) V := eq_refl.

Definition dirac {A} (v : A) : Meas A :=
  fun e => Indicator e v.

Lemma meas_id_left {A B} b (f : A -> Meas B) :
  dirac b >>= f = f b.
Proof.
  extensionality ev.
  unfold ">>=".
  unfold dirac.
  rewrite riemann_def_of_lebesgue_integration.
  setoid_rewrite integration_of_indicator.
  apply lebesgue_measure_interval.
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

Definition μ {e τ} (He : TC · ⊢ e : τ) : Meas (WT_Val τ) :=
  μEntropy >>= eval_in He.

Definition A_rel' (τ : Ty) (V_rel_τ : Val -> Val -> Type)
        (A0 A1 : Event Val) :=
  forall v0 v1 (Hv : V_rel_τ v0 v1),
    (A0 v0 = (* iff *) A1 v1).

Inductive E_rel' (τ : Ty) (V_rel_τ : Val -> Val -> Prop) (e0 e1 : Expr) : Prop :=
  mk_E_rel'
    (He0 : (TC · ⊢ e0 : τ))
    (He1 : (TC · ⊢ e1 : τ))
    (He : forall A0 A1,
        A_rel' τ V_rel_τ A0 A1 ->
        μ He0 A0 = μ He1 A1).

Definition V_rel_real (v0 v1 : Val) : Prop :=
  match (v0 : Expr), (v1 : Expr) with
  | e_real r0, e_real r1 => v0 = v1
  | _, _ => False
  end.

Definition V_rel_arrow
           (τa : Ty) (τr : Ty)
           (V_rel_a : Val -> Val -> Prop)
           (V_rel_r : Val -> Val -> Prop)
           (v0 v1 : Val) : Prop
  := match (v0 : Expr), (v1 : Expr) with
     | e_lam τa'0 body0, e_lam τa'1 body1  =>
       (τa = τa'0) ⨉ (τa = τa'1) ⨉
       exists (tc_body0 : (TC (extend · τa) ⊢ body0 : τr))
              (tc_body1 : (TC (extend · τa) ⊢ body1 : τr)),
       forall {va0 va1 : WT_Val τa},
           V_rel_a va0 va1 ->
           E_rel' τr V_rel_r body0.[(va0 : Expr)/] body1.[(va1 : Expr)/]
     | _, _ => False
     end.

Fixpoint V_rel τ : Val -> Val -> Prop :=
  match τ with
  | ℝ => V_rel_real
  | τa ~> τr => V_rel_arrow τa τr (V_rel τa) (V_rel τr)
  end.

Definition A_rel τ := A_rel' τ (V_rel τ).
Definition E_rel τ := E_rel' τ (V_rel τ).

Definition G_rel {Γ : Env Ty} {ρ0 ρ1 : WT_Env Γ} : Prop :=
  forall x v0 v1 τ,
    lookup Γ x = Some τ ->
    lookup ρ0 x = Some v0 ->
    lookup ρ1 x = Some v1 ->
    V_rel τ v0 v1.

Arguments G_rel _ _ _ : clear implicits.

Lemma G_rel_nil : G_rel · WT_nil WT_nil.
Proof.
  repeat intro.
  discriminate.
Qed.

Inductive related_exprs (Γ : Env Ty) (τ : Ty) (e0 e1 : Expr) : Prop :=
| mk_related_exprs
    (He0 : TC Γ ⊢ e0 : τ)
    (He1 : TC Γ ⊢ e1 : τ)
    (He : forall {ρ0 ρ1} (Hρ : G_rel Γ ρ0 ρ1),
        E_rel τ e0.[subst_of_WT_Env ρ0] e1.[subst_of_WT_Env ρ1]).

Arguments mk_related_exprs {_ _ _ _} _ _ _.

Notation "'EXP' Γ ⊢ e0 ≈ e1 : τ" :=
  (related_exprs Γ τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, no associativity).

Ltac decide_eval' He σ v w e u :=
  let not_ex := fresh "not_ex" in
  let focus_ev := fresh "focus_ev" in
  let focus_ew := fresh "focus_ew" in
  let uv := fresh "uv" in
  set (focus_ev := ev He σ);
set (focus_ew := ew He σ);
unfold ev in focus_ev;
unfold ew in focus_ew;
destruct (eval_dec He σ) as [[[uv w] [e u]] | not_ex];
[pose (v := mk_WT_Val uv (big_preservation He e));
replace focus_ev with (Some v) by auto;
subst focus_ev focus_ew;
assert (uv = (v : Val)) by auto;
clearbody v;
subst uv
|
subst focus_ev focus_ew;
try (contradict not_ex; eexists (_, _); repeat constructor; eassumption);
try solve [nnr]
].

Tactic Notation "decide_eval" "as"
       "[" ident(v) ident(w) ident(e) ident(u) "]"
  := match goal with
     | [ |- context[ev ?He ?σ] ] => decide_eval' He σ v w e u
     end.
Tactic Notation "decide_eval" constr(He) constr(σ) "as"
       "[" ident(v) ident(w) ident(e) ident(u) "]"
  :=  decide_eval' He σ v w e u.

Ltac what_equality_am_I_proving :=
  match goal with
  | [ |- @eq ?t ?l ?r ] => idtac "proving" l "=" r "at type" t
  | _ => idtac "it doesn't look like your goal is an equality"
  end.

Axiom int_const_entropy :
  forall (v : R+)
         (f : Entropy -> R+),
     (forall x, f x = v) ->
     Integration f μEntropy = v.

Lemma val_of_pure {e τ} :
  (TC · ⊢ e : τ) ->
  is_pure e ->
  is_val e.
Proof.
  intros.
  destruct e; try contradiction H; trivial.
  inversion X.
  discriminate.
Qed.

Definition WT_Val_of_pure {e τ} (He : (TC · ⊢ e : τ)) (Hp : is_pure e)
  : WT_Val τ := @mk_WT_Val _ (mk_Val e (val_of_pure He Hp)) He.

Lemma pure_is_atomic {e τ} A
      (He : (TC · ⊢ e : τ))
      (Hpure : is_pure e)
      σ :
  eval_in He σ A =
  Indicator A (WT_Val_of_pure He Hpure).
Proof.
  pose (WT_Val_of_pure He Hpure) as v'.
  assert (e = v') by auto.
  clearbody v'.
  subst.

  unfold eval_in.

  decide_eval as [v w ex u].
  simpl.
  inversion ex; subst; try absurd_Val.
  rewrite nnr_mult_1_r.
  apply WT_Val_eq in H0.
  subst.
  f_equal.
  apply WT_Val_eq.
  simpl.
  auto.
Qed.

Lemma pure_is_dirac {e τ}
      (He : TC · ⊢ e : τ)
      (Hpure : is_pure e) :
  μ He = dirac (WT_Val_of_pure He Hpure).
Proof.
  extensionality A.
  unfold μ, dirac; simpl.
  apply int_const_entropy; intro σ.
  rewrite (pure_is_atomic A He Hpure).
  reflexivity.
Qed.

Lemma compat_real Γ r :
  (EXP Γ ⊢ e_real r ≈ e_real r : ℝ).
Proof.
  refine (mk_related_exprs (TCReal _) (TCReal _) _).
  intros ρ0 ρ1 Hρ.
  simpl.

  exists (TCReal r) (TCReal r).
  intros A0 A1 HA.

  rewrite (pure_is_dirac (TCReal r) I).

  unfold dirac, Indicator; simpl.
  f_equal.
  apply HA.
  reflexivity.
Qed.

Lemma compat_var Γ x τ :
  lookup Γ x = Some τ ->
  EXP Γ ⊢ e_var x ≈ e_var x : τ.
Proof.
  intros Γx.
  refine (mk_related_exprs (TCVar _) (TCVar _) _); auto.
  intros ρ0 ρ1 Hρ.

  simpl.

  destruct (env_search (WT_Env_tc ρ0) Γx) as [v0 ρ0x].
  destruct (env_search (WT_Env_tc ρ1) Γx) as [v1 ρ1x].
  rewrite (subst_of_WT_Env_lookup ρ0x).
  rewrite (subst_of_WT_Env_lookup ρ1x).
  exists (WT_Val_tc v0) (WT_Val_tc v1).

  intros A0 A1 HA.

  specialize (Hρ _ _ _ _ Γx ρ0x ρ1x).

  assert (forall v : Val, is_pure v). {
    intros.
    destruct v as [[]]; try contradiction; constructor.
  }

  rewrite 2 (pure_is_dirac (WT_Val_tc _) (H _)).
  unfold dirac, Indicator; simpl.
  f_equal.
  apply HA.

  rewrite <- (@Val_eq v0) at 1 by auto.
  rewrite <- (@Val_eq v1) by auto.
  auto.
Qed.

Lemma extend_grel {Γ ρ0 ρ1 τ}
      (v0 v1 : WT_Val τ)
      (Hρ : G_rel Γ ρ0 ρ1)
      (Hv : V_rel τ v0 v1)
  : G_rel (extend Γ τ) (extend_WT_Env ρ0 v0) (extend_WT_Env ρ1 v1).
Proof.
  intros x v0' v1' τ' Γx ρ0x ρ1x.
  destruct x. {
    simpl in *.
    inversion Γx.
    inversion ρ0x.
    inversion ρ1x.
    subst.
    apply Hv.
  } {
    simpl in *.
    eapply Hρ; eauto.
  }
Qed.

Lemma compat_lam Γ body0 body1 τa τr :
  (EXP (extend Γ τa) ⊢ body0 ≈ body1 : τr) ->
  (EXP Γ ⊢ e_lam τa body0 ≈ e_lam τa body1 : (τa ~> τr)).
Proof.
  intros Hbody.
  destruct Hbody as [Hbody0 Hbody1 Hbodies]; simpl in *.
  refine (mk_related_exprs (TCLam Hbody0) (TCLam Hbody1) _).
  intros ρ0 ρ1 Hρ.

  pose proof body_subst ρ0 Hbody0 as Hbody0'.
  pose proof body_subst ρ1 Hbody1 as Hbody1'.

  exists (TCLam Hbody0') (TCLam Hbody1').
  intros A0 A1 HA.

  (* can't rewrite these directly, who knows why? *)
  enough (dirac (WT_Val_of_pure (TCLam Hbody0') I) A0 =
          dirac (WT_Val_of_pure (TCLam Hbody1') I) A1). {
    rewrite <- 2 (pure_is_dirac (TCLam _) I) in H.
    exact H.
  }

  unfold dirac, Indicator; simpl.
  f_equal.
  apply HA.

  split; auto.
  exists Hbody0'.
  exists Hbody1'.

  intros va0 va1 Hva.

  specialize (Hbodies _ _ (extend_grel va0 va1 Hρ Hva)).
  autosubst.
Qed.

Axiom prod_meas : forall {A B}, Meas A -> Meas B -> Meas (A * B).

Lemma tonelli_1 :
  forall {A B} (f : A -> B -> R+) (μx : Meas A) (μy : Meas B),
    Integration (fun x => Integration (fun y => f x y) μy) μx =
    Integration (fun xy => f (fst xy) (snd xy)) (prod_meas μx μy).
Admitted.

Lemma tonelli_2 :
  forall {A B} (f : A -> B -> R+) (μx : Meas A) (μy : Meas B),
    Integration (fun xy => f (fst xy) (snd xy)) (prod_meas μx μy) =
    Integration (fun y => Integration (fun x => f x y) μx) μy.
Admitted.

Inductive SigmaFinite : forall {A}, Meas A -> Prop :=
| ent_finite : SigmaFinite μEntropy
| leb_finite : SigmaFinite lebesgue_measure.
Hint Constructors SigmaFinite.

Lemma tonelli_3 :
  forall {A B} (f : A -> B -> R+) (μx : Meas A) (μy : Meas B),
    SigmaFinite μx ->
    SigmaFinite μy ->
    Integration (fun x => Integration (fun y => f x y) μy) μx =
    Integration (fun y => Integration (fun x => f x y) μx) μy.
Admitted.

Definition preimage {A B C} (f : A -> B) : (B -> C) -> (A -> C) :=
  fun eb a => eb (f a).

(* Lemma 3 *)
Lemma coarsening :
  forall {X}
         (M : Event X -> Event X -> Prop)
         (μ0 μ1 : Meas X)
         (f0 f1 : X -> R+)
         (μs_agree : forall A0 A1, M A0 A1 -> μ0 A0 = μ1 A1)
         (f_is_M_measurable :
            forall (B : Event R+),
              M (preimage f0 B) (preimage f1 B)),
    Integration f0 μ0 = Integration f1 μ1.
Proof.
  intros.
  rewrite riemann_def_of_lebesgue_integration.
  apply eq_sym.
  rewrite riemann_def_of_lebesgue_integration.
  apply eq_sym.

  integrand_extensionality t.
  apply μs_agree.

  specialize (f_is_M_measurable (fun fx => bool_of_dec (fx [>] t))).
  unfold preimage in f_is_M_measurable.
  exact f_is_M_measurable.
Qed.

(* Lemma 5 *)
Axiom integration_πL_πR : forall (g : Entropy -> Entropy -> R+),
    Integration (fun σ => g (πL σ) (πR σ)) μEntropy =
    Integration (fun σL => Integration (fun σR => g σL σR) μEntropy) μEntropy.

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

(* Theorem 1 *)
Theorem μe_eq_μEntropy :
  forall {e τ B}
    (He : TC · ⊢ e : τ)
    (f : WT_Val τ -> Meas B),
    μ He >>= f =
    μEntropy >>=
             (fun σ A =>
                option0 ((fun v => f v A) <$> ev He σ) [*] ew He σ).
Proof.
  intros.

  unfold μ, ">>=".

  extensionality A.

  rewrite riemann_def_of_lebesgue_integration.
  rewrite tonelli_3; auto.
  unfold eval_in.

  integrand_extensionality σ.

  rewrite <- Integration_linear_mult_r.
  f_equal.

  destruct (ev _ _); simpl. {
    pose proof integration_of_indicator lebesgue_measure.
    unfold Indicator in *.
    rewrite H.
    apply lebesgue_measure_interval.
  } {
    replace (fun _ => nnr_0) with (fun _ : R => nnr_0 [*] nnr_0)
      by (extensionality z; nnr; apply Rmult_0_l).
    rewrite <- Integration_linear_mult_r.
    nnr.
  }
Qed.

(* used to push the option0 into the very inside *)
Lemma μe_eq_μEntropy2 {τ0 τ1 B}
      (f : WT_Val τ0 -> WT_Val τ1 -> Meas B)
      {e0 e1}
      (He0 : (TC · ⊢ e0 : τ0))
      (He1 : (TC · ⊢ e1 : τ1)) :
  μ He0 >>= (fun v0 => μ He1 >>= (fun v1 => f v0 v1)) =
  μEntropy >>=
           (fun σ0 =>
              μEntropy >>=
                       (fun σ1 A =>
                          option0 ((fun v0 v1 => f v0 v1 A)
                                     <$> ev He0 σ0 <*> ev He1 σ1)
                                  [*] ew He1 σ1 [*] ew He0 σ0)).
Proof.
  extensionality A.
  setoid_rewrite μe_eq_μEntropy; eauto.
  rewrite μe_eq_μEntropy.
  integrand_extensionality σ0.

  unfold ">>=".
  rewrite <- Integration_linear_mult_r.
  f_equal.

  decide_eval as [v0 w0 ex0 u0]; simpl; auto.
  rewrite <- Integration_linear_mult_l.
  nnr.
Qed.

Definition plus_in (v v' : WT_Val ℝ) : Meas (WT_Val ℝ) :=
  fun A =>
    match (v : Expr), (v' : Expr) with
    | e_real r, e_real r' =>
      Indicator A (v_real (r + r'))
    | _, _ => nnr_0
    end.

Lemma by_μe_eq_μEntropy_plus {el er}
  (Hel : TC · ⊢ el : ℝ)
  (Her : TC · ⊢ er : ℝ) :
  μEntropy >>= eval_in (TCPlus Hel Her) =
  μ Hel >>= (fun vl => μ Her >>= (fun vr => plus_in vl vr)).
Proof.
  extensionality A.

  rewrite μe_eq_μEntropy2.
  set (f σ0 σ1 A :=
         option0 (((fun vl vr => plus_in vl vr A) <$> ev Hel σ0) <*> ev Her σ1)
                 [*] ew Her σ1 [*] ew Hel σ0).
  transitivity ((μEntropy >>= (fun σ => f (π 0 σ) (π 1 σ))) A). {
    subst f.
    simpl.

    integrand_extensionality σ.

    unfold eval_in.
    decide_eval (TCPlus Hel Her) σ as [v0 w0 ex0 u0]; simpl. {
      inversion ex0; try absurd_Val; subst.

      simpl.

      decide_eval as [v3 w3 ex3 u3]; simpl.
      decide_eval as [v4 w4 ex4 u4]; simpl.

      destruct_WT_Val v0.
      destruct_WT_Val v3.
      destruct_WT_Val v4.
      inversion H; subst.
      simpl in *.

      specialize (u3 (_, _) X).
      specialize (u4 (_, _) X0).
      inversion u3; subst.
      inversion u4; subst.

      unfold plus_in; simpl.
      rewrite nnr_mult_assoc.
      f_equal.
      apply nnr_mult_comm.
    } {
      decide_eval as [v3 w3 ex3 u3].
      decide_eval as [v4 w4 ex4 u4].
      contradict not_ex.

      destruct_WT_Val v3.
      destruct_WT_Val v4.

      eexists (_, _).
      refine (EPlus _ _ _); eauto.
    }
  } {
    rewrite pick_2_entropies.
    auto.
  }
Qed.

(* A version of A_rel that works on well typed values;
   it turns out to be equivalent to the original *)
Definition WT_A_rel (τ : Ty) (A0 A1 : Event (WT_Val τ)) :=
  forall (v0 v1 : WT_Val τ) (Hv : V_rel τ v0 v1),
    (A0 v0 = (* iff *) A1 v1).

Definition narrow_event {τ} (A : Event (WT_Val τ)) : Event Val :=
  fun v =>
    match decidable_tc · v with
    | inl (existT _ τ' tc) =>
      match ty_eq_dec τ' τ with
      | left Heq => A (mk_WT_Val _ (rew Heq in tc))
      | right _ => false
      end
    | inr _ => false
    end.

Lemma narrow_cast_inverse τ (A : Event (WT_Val τ)) :
  (narrow_event A : Event (WT_Val τ)) = A .
Proof.
  extensionality v.
  destruct v.
  unfold narrow_event.
  simpl.
  destruct decidable_tc as [[]|]. {
    destruct ty_eq_dec. {
      subst.
      do 2 f_equal.
      compute.
      eapply tc_unique.
    } {
      contradict n.
      eapply expr_type_unique; eauto.
    }
  } {
    contradict n.
    repeat econstructor; eauto.
  }
Qed.

Lemma V_rel_implies_TC {τ v0 v1} :
  V_rel τ v0 v1 ->
  inhabited (TC · ⊢ v0 : τ) /\ inhabited (TC · ⊢ v1 : τ).
Proof.
  intros.
  destruct τ;
destruct v0 using Val_rect;
destruct v1 using Val_rect;
try contradiction H;
try solve [repeat constructor]. {
    inversion H as [[? ?] [? [? _]]].
    repeat subst.
    repeat econstructor; eauto.
  }
Qed.

Lemma A_rels_equiv τ (A0 A1 : Event Val) :
  WT_A_rel τ A0 A1 <-> A_rel τ A0 A1.
Proof.
  split. {
    intros HA v0 v1 Hv.
    destruct (V_rel_implies_TC Hv) as [[Hv0] [Hv1]].
    specialize (HA (mk_WT_Val _ Hv0) (mk_WT_Val _ Hv1) Hv).
    unfold narrow_event in HA.
    apply HA.
  } {
    rewrite <- (narrow_cast_inverse τ A0).
    rewrite <- (narrow_cast_inverse τ A1).
    intros HA v0 v1 Hv.
    unfold narrow_event.
    destruct (V_rel_implies_TC Hv) as [[] []].
    repeat destruct decidable_tc; auto. {
      destruct s, s0.
      pose proof (expr_type_unique t X).
      pose proof (expr_type_unique t0 X0).
      subst.
      destruct ty_eq_dec; auto.
    } {
      contradict n.
      eexists; eauto.
    } {
      contradict n.
      eexists; eauto.
    }
  }
Qed.

Lemma use_equiv_A_rel {τ e0 e1}
      (He0 : TC · ⊢ e0 : τ)
      (He1 : TC · ⊢ e1 : τ)
      (Hμ : forall (A0 A1 : Event Val),
          A_rel τ A0 A1 ->
          μ He0 A0 = μ He1 A1)
      {A0 A1 : Event (WT_Val τ)}
      (HA : WT_A_rel τ A0 A1) :
  μ He0 A0 = μ He1 A1.
Proof.
    setoid_rewrite <- A_rels_equiv in Hμ.
    specialize (Hμ (narrow_event A0) (narrow_event A1)).
    repeat rewrite narrow_cast_inverse in Hμ.
    apply Hμ, HA.
Qed.

Lemma work_of_plus
      {el0 er0 el1 er1 : Expr}
      (Hel0 : TC · ⊢ el0 : ℝ)
      (Her0 : TC · ⊢ er0 : ℝ)
      (Hel1 : TC · ⊢ el1 : ℝ)
      (Her1 : TC · ⊢ er1 : ℝ)
      (Hl : forall Al0 Al1 : Event Val,
          A_rel ℝ Al0 Al1 ->
          μ Hel0 Al0 = μ Hel1 Al1)
      (Hr : forall Ar0 Ar1 : Event Val,
          A_rel ℝ Ar0 Ar1 ->
          μ Her0 Ar0 = μ Her1 Ar1)
      {A0 A1 : Event Val}
      (HA : A_rel ℝ A0 A1)
  : μ (TCPlus Hel0 Her0) A0 = μ (TCPlus Hel1 Her1) A1.
Proof.
  unfold μ.

  do 2 rewrite by_μe_eq_μEntropy_plus.

  apply (coarsening (WT_A_rel ℝ)); try solve [apply use_equiv_A_rel; auto].
  intros B vl0 vl1 Hvl.
  unfold preimage.
  f_equal.

  apply (coarsening (WT_A_rel ℝ)); try solve [apply use_equiv_A_rel; auto].
  intros B0 vr0 vr1 Hvr.
  unfold preimage.
  f_equal.

  destruct_WT_Val vl0.
  destruct_WT_Val vl1.
  destruct_WT_Val vr0.
  destruct_WT_Val vr1.
  unfold plus_in.
  simpl in *.

  inversion Hvl.
  inversion Hvr.
  subst.

  unfold Indicator.
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

  destruct Hl as [tc_l0 tc_l1 Hl].
  destruct Hr as [tc_r0 tc_r1 Hr].
  simpl in *.
  refine (mk_related_exprs (TCPlus tc_l0 tc_r0) (TCPlus tc_l1 tc_r1) _).
  simpl in *.
  intros ρ0 ρ1 Hρ.

  specialize (Hl _ _ Hρ).
  specialize (Hr _ _ Hρ).

  destruct Hl as [tc_l0' tc_l1' Hl].
  destruct Hr as [tc_r0' tc_r1' Hr].

  exists (TCPlus tc_l0' tc_r0') (TCPlus tc_l1' tc_r1').

  intros A0 A1 HA.

  apply work_of_plus; auto.
Qed.

Definition apply_in {τa τr}
        (vf : WT_Val (τa ~> τr))
        (va : WT_Val τa)
        (σ : Entropy)
  : Meas (WT_Val τr) :=
  WT_Val_arrow_rect
    (const (Meas _))
    (fun body Hbody => eval_in (ty_subst1 va Hbody) σ)
    vf.

(* ugly, ugly proof, relies on internals of WT_Val_arrow_rect *)
Lemma elim_apply_in {τa τr}
      (vlam : WT_Val (τa ~> τr))
  : {body : Expr &
    {Hbody : (TC (extend · τa) ⊢ body : τr) &
     (vlam : Expr) = e_lam τa body /\
     forall
       (va : WT_Val τa) ,
       apply_in vlam va =
       eval_in (ty_subst1 va Hbody)}}.
Proof.
  destruct_WT_Val vlam.
  exists body.
  exists Hbody.

  simpl.
  intuition idtac.

  extensionality σ.
  simpl.
  unfold eq_rect_r.
  repeat
    (match goal with
     | [ |- context[ rew ?H in _ ] ] =>
       let z := type of H in
       replace H with (eq_refl : z) by apply proof_irrelevance
     end; simpl).
  reflexivity.
Qed.

(* ok, let's never look inside apply_in ever again. It's too ugly *)
Global Opaque apply_in.

Ltac do_elim_apply_in :=
  match goal with
  | [ |- context[ apply_in ?vlam ?va ] ] =>
    let body := fresh "body" in
    let Hbody := fresh "H" body in
    let Hvf_body := fresh "Hvf_body" in
    let H := fresh "H" in
    destruct (elim_apply_in vlam) as [body [Hbody [Hvf_body H]]];
    try (rewrite H;
         inversion Hvf_body;
         clear H Hvf_body)
  end.

(* Lemma option0_map f g : *)
(*   option0 (f <$> g) = (option0 ∘ f) <$> g. *)

Lemma by_μe_eq_μEntropy_app {ef ea τa τr}
      (Hef : TC · ⊢ ef : (τa ~> τr))
      (Hea : TC · ⊢ ea : τa) :
  μEntropy >>= eval_in (TCApp Hef Hea) =
  μ Hef >>= (fun vf => μ Hea >>= (fun va => μEntropy >>= apply_in vf va)).
Proof.
  extensionality A.

  rewrite μe_eq_μEntropy2.
  set (x σf σa σbody A :=
         option0 ((fun vf va => apply_in vf va σbody A)
                    <$> ev Hef σf
                    <*> ev Hea σa)
                 [*] ew Hea σa [*] ew Hef σf).
  transitivity ((μEntropy >>= (fun σ => x (π 0 σ) (π 1 σ) (π 2 σ))) A). {
    subst x.
    simpl.

    integrand_extensionality σ.

    unfold eval_in.
    decide_eval (TCApp Hef Hea) σ as [v0 w0 ex0 u0]; simpl. {
      inversion ex0; subst; try absurd_Val.
      decide_eval as [v4 w4 ex4 u4]; simpl.
      decide_eval as [v5 w5 ex5 u5]; simpl.
      do_elim_apply_in.

      destruct_WT_Val v4.

      specialize (u4 (_, _) X).
      specialize (u5 (_, _) X0).
      inversion u4; subst.
      inversion u5; subst.
      inversion H1; subst.

      unfold eval_in.

      decide_eval as [v6 w6 ex6 u6]. {
        simpl.

        specialize (u6 (v0 : Val, w3) X1).
        inversion u6; subst.
        simpl.
        enough (v0 = v6) by (rewrite H; nnr).
        apply WT_Val_eq.
        rewrite H0.
        auto.
      }
    } {
      decide_eval as [v3 w3 ex3 u3].
      decide_eval as [v4 w4 ex4 u4].
      destruct_WT_Val v3.
      simpl.
      do_elim_apply_in; subst.
      unfold eval_in; simpl.

      decide_eval as [v5 w5 ex5 u5].
      contradict not_ex.
      eexists (_, _).
      econstructor; eauto.
    }
  } {
    rewrite pick_3_entropies.
    integrand_extensionality σf.
    integrand_extensionality σa.
    subst x.
    simpl.
    unfold ">>=".
    rewrite <- 2 Integration_linear_mult_r.
    do 2 f_equal.

    decide_eval Hef σf as [v0 w0 ex0 u0]; simpl. {
      decide_eval Hea σa as [v1 w1 ex1 u1]; simpl; auto.
      apply int_const_entropy; auto.
    } {
      apply int_const_entropy; auto.
    }
  }
Qed.

Lemma work_of_app {τa τr}
      {ef0 ea0 ef1 ea1 : Expr}
      (Hef0 : TC · ⊢ ef0 : τa ~> τr)
      (Hea0 : TC · ⊢ ea0 : τa)
      (Hef1 : TC · ⊢ ef1 : τa ~> τr)
      (Hea1 : TC · ⊢ ea1 : τa)
      (Hf : forall Af0 Af1 : Event Val,
          A_rel (τa ~> τr) Af0 Af1 ->
          μ Hef0 Af0 = μ Hef1 Af1)
      (Ha : forall Aa0 Aa1 : Event Val,
          A_rel τa Aa0 Aa1 ->
          μ Hea0 Aa0 = μ Hea1 Aa1)
      {A0 A1 : Event Val}
      (HA : A_rel τr A0 A1)
  : μ (TCApp Hef0 Hea0) A0 = μ (TCApp Hef1 Hea1) A1.
Proof.
  unfold μ.

  do 2 rewrite by_μe_eq_μEntropy_app.

  apply (coarsening (WT_A_rel (τa ~> τr)));
try solve [apply use_equiv_A_rel; auto].
  intros B vf0 vf1 Hvf.
  unfold preimage.
  f_equal.

  apply (coarsening (WT_A_rel τa));
try solve [apply use_equiv_A_rel; auto].
  intros B0 va0 va1 Hva.
  unfold preimage.
  f_equal.

  destruct_WT_Val vf0.
  destruct_WT_Val vf1.

  simpl in *.
  hnf in Hvf.
  destruct Hvf as [_ [_ [_ Hvf]]].
  specialize (Hvf va0 va1 Hva).
  destruct Hvf as [tc_body0 tc_body1 Hvf].
  specialize (Hvf A0 A1 HA).

  do_elim_apply_in.
  do_elim_apply_in.
  subst.
  replace (ty_subst1 _ _) with tc_body0 by apply tc_unique.
  replace (ty_subst1 _ _) with tc_body1 by apply tc_unique.
  apply Hvf.
Qed.

Lemma compat_app Γ ef0 ef1 ea0 ea1 τa τr :
  (EXP Γ ⊢ ef0 ≈ ef1 : (τa ~> τr)) ->
  (EXP Γ ⊢ ea0 ≈ ea1 : τa) ->
  (EXP Γ ⊢ e_app ef0 ea0 ≈ e_app ef1 ea1 : τr).
Proof.
  intros Hf Ha.

  destruct Hf as [tc_f0 tc_f1 Hf].
  destruct Ha as [tc_a0 tc_a1 Ha].
  simpl in *.
  refine (mk_related_exprs (TCApp tc_f0 tc_a0) (TCApp tc_f1 tc_a1) _).
  simpl.
  intros ρ0 ρ1 Hρ.

  specialize (Hf _ _ Hρ).
  specialize (Ha _ _ Hρ).
  destruct Hf as [tc_f0' tc_f1' Hf].
  destruct Ha as [tc_a0' tc_a1' Ha].

  eexists (TCApp tc_f0' tc_a0') (TCApp tc_f1' tc_a1').
  intros A0 A1 HA.

  apply work_of_app; auto.
Qed.

Lemma compat_sample Γ :
  EXP Γ ⊢ e_sample ≈ e_sample : ℝ.
Proof.
  refine (mk_related_exprs TCSample TCSample _).
  simpl.
  intros ρ0 ρ1 Hρ.
  exists TCSample TCSample.
  intros A0 A1 HA.

  unfold μ.
  f_equal.
  extensionality v.

  apply HA.
  destruct_WT_Val v.
  reflexivity.
Qed.

Definition factor_in (v : WT_Val ℝ) : Meas (WT_Val ℝ) :=
  fun A =>
    match (v : Expr) with
    | e_real r =>
      match Rle_dec 0 r with
      | left rpos => Indicator A (v_real r) [*] mknnr r rpos
      | _ => nnr_0
      end
    | _ => nnr_0
    end.

Lemma by_μe_eq_μEntropy_factor {e}
      (He : (TC · ⊢ e : ℝ)) :
  μEntropy >>= eval_in (TCFactor He) =
  μ He >>= factor_in.
Proof.
  extensionality A.

  rewrite μe_eq_μEntropy; eauto.

  integrand_extensionality σ.
  unfold option_map, factor_in, eval_in.

  decide_eval as [v0 w0 ex0 u0]. {
    destruct_WT_Val v0.
    inversion ex0; try absurd_Val.
    subst.
    decide_eval as [v1 w1 ex1 u1].
    destruct_WT_Val v1.
    simpl in *.
    injection (u1 (_, _) X); intros.
    subst.
    destruct Rle_dec; [| contradiction].
    set (mk_WT_Val _ _).
    rewrite (@WT_Val_eq _ (v_real r) w0); [nnr |].
    auto.
  } {
    simpl.
    decide_eval as [v1 w1 ex1 u1].
    destruct_WT_Val v1.
    simpl in *.
    destruct Rle_dec; try solve [nnr].

    contradict not_ex.
    eexists (v_real r : Val, _).
    eapply EFactor with (rpos := r0).
    eauto.
  }
Qed.

Lemma work_of_factor
  (e0 e1 : Expr)
  (He0 : TC · ⊢ e0 : ℝ)
  (He1 : TC · ⊢ e1 : ℝ)
  (He : forall A0 A1 : Event Val,
      A_rel' ℝ (V_rel ℝ) A0 A1 ->
      μ He0 A0 = μ He1 A1)
  (A0 A1 : Event Val)
  (HA : A_rel' ℝ (V_rel ℝ) A0 A1) :
  μ (TCFactor He0) A0 = μ (TCFactor He1) A1.
Proof.
  unfold μ.

  rewrite (by_μe_eq_μEntropy_factor He0).
  rewrite (by_μe_eq_μEntropy_factor He1).

  apply (coarsening (WT_A_rel ℝ)); try solve [apply use_equiv_A_rel; auto].
  intros B v0 v1 Hv.
  unfold preimage.
  f_equal.

  destruct_WT_Val v0.
  destruct_WT_Val v1.
  simpl in *.

  unfold factor_in.
  simpl.

  inversion Hv.
  subst.

  destruct Rle_dec; auto.
  unfold Indicator.
  do 2 f_equal.
  apply HA.
  exact Hv.
Qed.

Lemma compat_factor Γ e0 e1:
  (EXP Γ ⊢ e0 ≈ e1 : ℝ) ->
  (EXP Γ ⊢ e_factor e0 ≈ e_factor e1 : ℝ).
Proof.
  intro He.
  destruct He as [TC0 TC1 He].
  refine (mk_related_exprs (TCFactor TC0) (TCFactor TC1) _).

  intros ρ0 ρ1 Hρ.

  specialize (He _ _ Hρ).
  destruct He as [TC0' TC1' He].

  exists (TCFactor TC0') (TCFactor TC1').
  intros A0 A1 HA.

  apply work_of_factor; auto.
Qed.

Lemma fundamental_property {Γ e τ} :
  (TC Γ ⊢ e : τ) ->
  (EXP Γ ⊢ e ≈ e : τ).
Proof.
  intros tc.
  induction tc.
  - apply compat_real.
  - apply compat_var; tauto.
  - apply compat_lam; tauto.
  - apply compat_app with (τa := τa); tauto.
  - apply compat_factor; tauto.
  - apply compat_sample.
  - apply compat_plus; tauto.
Qed.

Print Assumptions fundamental_property.

Lemma fundamental_property_of_values {τ} (v : Val) :
  (TC · ⊢ v : τ) ->
  (V_rel τ v v).
Proof.
  intros.
  destruct v using Val_rect; simpl in *. {
    inversion X; subst.
    reflexivity.
  } {
    inversion X; subst.
    split; auto.
    exists X0.
    exists X0.
    intros.
    pose proof fundamental_property X0.
    destruct H0.
    pose (ρ0 := extend_WT_Env WT_nil va0).
    pose (ρ1 := extend_WT_Env WT_nil va1).
    specialize (He ρ0 ρ1).
    assert (G_rel (extend · τa) ρ0 ρ1). {
      hnf.
      intros.
      destruct x; try discriminate.
      inversion H0.
      inversion H1.
      inversion H2.
      subst.
      auto.
    }
    specialize (He H0).
    clear H0.

    destruct WT_nil as [? Hnil].
    inversion Hnil; subst.
    auto.
  }
Qed.
