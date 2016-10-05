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

(* setoid rewriting under lambda *)
(* http://coq-club.inria.narkive.com/PbdQR4E7/rewriting-under-abstractions *)
Require Import Setoid Morphisms Program.Syntax.
Instance refl_respectful {A B RA RB}
         `(sa : subrelation A RA eq)
         `(sb : subrelation B eq RB)
  : Reflexive (RA ++> RB)%signature.
Proof.
  intros f x x' Hxx'.
  apply sb.
  f_equal.
  apply sa; auto.
Qed.

Instance subrel_eq_respect {A B RA RB}
         `(sa : subrelation A RA eq)
         `(sb : subrelation B eq RB)
  : subrelation eq (respectful RA RB).
Proof.
  intros f g Hfg.
  intros a a' Raa'.
  apply sb.
  f_equal.
  apply sa; auto.
Qed.

Instance pointwise_eq_ext {A B RB}
         `(sb : subrelation B RB (@eq B))
  : subrelation (pointwise_relation A RB) eq.
Proof.
  intros f g Hfg.
  extensionality x.
  apply sb.
  apply (Hfg x).
Qed.

Instance eq_pointwise {A B RB}
         `(sb : subrelation B (@eq B) RB) :
  subrelation eq (pointwise_relation A RB).
Proof.
  intros f g Hfg x.
  apply sb.
  subst.
  reflexivity.
Qed.


Definition Event X := X -> bool.

(* Axiom eval_dec : *)
(*   forall ρ e σ, *)
(*     (existsT! vw : (Val * R+), let (v, w) := vw in EVAL ρ, σ ⊢ e ⇓ v, w) + *)
(*     ((existsT vw : (Val * R+), let (v, w) := vw in EVAL ρ, σ ⊢ e ⇓ v, w) -> False). *)

Definition eval_dec :
  forall {Γ ρ e τ},
    (ENV ρ ⊨ Γ) ->
    (TC Γ ⊢ e : τ) ->
    forall σ,
      (existsT! vw : (Val * R+), let (v, w) := vw in EVAL ρ, σ ⊢ e ⇓ v, w) +
      ((existsT vw : (Val * R+), let (v, w) := vw in EVAL ρ, σ ⊢ e ⇓ v, w) -> False)
  := @determinism.eval_dec.

Definition big_preservation :
  forall {Γ ρ e τ v w},
    (ENV ρ ⊨ Γ) ->
    (TC Γ ⊢ e : τ) ->
    forall σ,
      (EVAL ρ, σ ⊢ e ⇓ v, w) ->
      (TCV ⊢ v : τ)
  := @determinism.big_preservation.

Lemma eval_a_preservation :
  forall {Γ ρ ae τ},
    (ENV ρ ⊨ Γ) ->
    (TC Γ ⊢ e_pure ae : τ) ->
    {v : WT_Val τ & eval_a ρ ae = Some (projT1 v)}.
Proof.
  intros.
  inversion H; subst; simpl. {
    exists (existT _ (v_real r) (TCVReal r)); auto.
  } {
    destruct (env_search X _ _ H1) as [v ?].
    exists v; auto.
  } {
    assert (WT_Val (τa ~> τr)). {
      exists (v_clo τa body ρ).
      econstructor; eauto.
    }
    exists (existT _ (v_clo τa body ρ) (TCVClo X H1)); auto.
  }
Defined.

Definition eval_a_wt {Γ ρ ae τ} (Hρ : ENV ρ ⊨ Γ) (Hae : TC Γ ⊢ e_pure ae : τ) : WT_Val τ :=
  projT1 (eval_a_preservation Hρ Hae).

Definition ev {Γ ρ e τ} (Hρ : ENV ρ ⊨ Γ) (He : TC Γ ⊢ e : τ) σ : option (WT_Val τ) :=
  match eval_dec Hρ He σ with
  | inl (existT _ (v, w) (evl, _)) =>
    Some (existT _ v (big_preservation Hρ He σ evl))
  | inr _ => None
  end.

Definition ew {Γ ρ e τ} (Hρ : ENV ρ ⊨ Γ) (He : TC Γ ⊢ e : τ) σ : R+ :=
  match eval_dec Hρ He σ with
  | inl (existT _ (v, w) _) => w
  | inr _ => nnr_0
  end.

Definition resist_folding {A} (x : A) := x.

Definition ifte {X} (a : bool) (b c : X) := if a then b else c.
Definition Indicator {X} (b : Event X) : X -> R+ := fun x => ifte (b x) nnr_1 nnr_0.


Definition eval_in {Γ ρ e τ} (Hρ : ENV ρ ⊨ Γ) (He : TC Γ ⊢ e : τ) (A : Event (WT_Val τ)) σ : R+ :=
  option0 (Indicator A <$> ev Hρ He σ) [*] ew Hρ He σ.

Definition Meas A := (Event A -> R+).
Axiom μEntropy : Meas Entropy.

Axiom Integration : forall {A}, (A -> R+) -> Meas A -> R+.
(* Notation "'∫' fx ';' μ ( 'd' x )" := (Integration (fun x => fx) μ). *)

Ltac integrand_extensionality x :=
  match goal with
  | [ |- Integration ?f ?μ = Integration ?g ?μ] => f_equal; extensionality x
  | _ => fail "not an equality between integrals on the same measure"
  end.

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

Definition widen_event {τ} (e : Event Val) : Event (WT_Val τ) :=
  fun vτ => e (projT1 vτ).

Definition μ {Γ ρ e τ} (Hρ : ENV ρ ⊨ Γ) (He : TC Γ ⊢ e : τ) : Meas (WT_Val τ) :=
  fun V => Integration (fun σ => eval_in Hρ He V σ) μEntropy.

Definition A_rel' (τ : Ty) (V_rel_τ : Val -> Val -> Type)
        (A0 A1 : Event Val) :=
  forall v0 v1 (Hv : V_rel_τ v0 v1),
    (A0 v0 = (* iff *) A1 v1).

Definition E_rel' (τ : Ty) (V_rel_τ : Val -> Val -> Prop) (c0 c1 : Config τ) : Prop :=
  let (Γ0, ρ0, Hρ0, e0, He0) := c0 in
  let (Γ1, ρ1, Hρ1, e1, He1) := c1 in
  forall A0 A1,
    A_rel' τ V_rel_τ A0 A1 ->
    μ Hρ0 He0 (widen_event A0) = μ Hρ1 He1 (widen_event A1).

Definition V_rel_real (v0 v1 : Val) : Prop :=
  match v0, v1 with
  | v_real r0, v_real r1 => v0 = v1
  | _, _ => False
  end.

(* Record V_rel_arrow_record *)
(*        {τa τr : Ty} {V_rel_a V_rel_r : Val -> Val -> Prop} *)
(*        {x0 x1 : Var} {body0 body1 : Expr} {ρ_clo0 ρ_clo1 : Env Val} *)
(*   : Prop *)
(*   := {  *)
(* V_rel_Γ_clo0 : Env Ty; *)
(*        V_rel_Hρ_clo0 : ENV ρ_clo0 ⊨ V_rel_Γ_clo0; *)
(*        V_rel_tc_body0 : (TC (extend V_rel_Γ_clo0 x0 τa) ⊢ body0 : τr); *)
(*        V_rel_Γ_clo1 : Env Ty; *)
(*        V_rel_Hρ_clo1 : ENV ρ_clo1 ⊨ V_rel_Γ_clo1; *)
(*        V_rel_tc_body1 : (TC (extend V_rel_Γ_clo1 x1 τa) ⊢ body1 : τr); *)
(*        V_rel_thingy : *)
(*          forall {va0 va1} *)
(*                 (tc_va0 : (TCV ⊢ va0 : τa)) *)
(*                 (tc_va1 : (TCV ⊢ va1 : τa)), *)
(*            V_rel_a va0 va1 -> *)
(*            E_rel τr V_rel_r *)
(*                  (mk_config (env_model_extend V_rel_Hρ_clo0 tc_va0) V_rel_tc_body0) *)
(*                  (mk_config (env_model_extend V_rel_Hρ_clo1 tc_va1) V_rel_tc_body1) *)
(*      }. *)

Definition V_rel_arrow
           (τa : Ty) (τr : Ty)
           (V_rel_a : Val -> Val -> Prop)
           (V_rel_r : Val -> Val -> Prop)
           (v0 v1 : Val) : Prop
  := match v0, v1 with
     | v_clo τa'0 body0 ρ_clo0, v_clo τa'1 body1 ρ_clo1 =>
       (τa = τa'0) ⨉ (τa = τa'1) ⨉
       exists Γ_clo0
              (Hρ_clo0 : ENV ρ_clo0 ⊨ Γ_clo0)
              (tc_body0 : (TC (extend Γ_clo0 τa) ⊢ body0 : τr)),
       exists Γ_clo1
              (Hρ_clo1 : ENV ρ_clo1 ⊨ Γ_clo1)
              (tc_body1 : (TC (extend Γ_clo1 τa) ⊢ body1 : τr)),
       forall {va0 va1 : WT_Val τa},
           V_rel_a (projT1 va0) (projT1 va1) ->
           E_rel' τr V_rel_r
                  (mk_config (env_model_extend Hρ_clo0 va0) tc_body0)
                  (mk_config (env_model_extend Hρ_clo1 va1) tc_body1)
     | _, _ => False
     end.

Reserved Notation "'VREL' v0 , v1 ∈ V[ τ ]"
         (at level 69, v0 at level 99, v1 at level 99, τ at level 99).
Fixpoint V_rel τ : Val -> Val -> Prop :=
  match τ with
  | ℝ => V_rel_real
  | τa ~> τr => V_rel_arrow τa τr (V_rel τa) (V_rel τr)
  end.

Notation "'VREL' v0 , v1 ∈ V[ τ ]" := (V_rel τ v0 v1).

Definition A_rel τ := A_rel' τ (V_rel τ).
Definition E_rel τ := E_rel' τ (V_rel τ).

Notation "'EREL' e0 , e1 ∈ E[ τ ]" :=
  (E_rel τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, τ at level 99).
Notation "'AREL' A0 , A1 ∈ A[ τ ]" :=
  (A_rel τ A0 A1)
    (at level 69, A0 at level 99, A1 at level 99, τ at level 99).


Record G_rel {Γ : Env Ty} {ρ0 ρ1 : Env Val} : Type :=
  mk_G_rel {
      G_rel_modeling0 : ENV ρ0 ⊨ Γ;
      G_rel_modeling1 : ENV ρ1 ⊨ Γ;
      G_rel_V : forall {x v0 v1 τ},
          lookup Γ x = Some τ ->
          lookup ρ0 x = Some v0 ->
          lookup ρ1 x = Some v1 ->
          V_rel τ v0 v1
    }.

Arguments G_rel _ _ _ : clear implicits.
Notation "'GREL' ρ0 , ρ1 ∈ G[ Γ ]" :=
  (G_rel Γ ρ0 ρ1)
    (at level 69, ρ0 at level 99, ρ1 at level 99, Γ at level 99).

(* Definition related_expr (Γ : Env Ty) (e : Expr) (τ : Ty) : Type := *)
(*   {He : (TC Γ ⊢ e : τ) & *)
(*         forall {ρ} (Hρ : dGREL ρ ∈ G[Γ]), *)
(*           (dEREL (mk_config (dG_rel_modeling Hρ) He) ∈ E[τ])}. *)

Record related_exprs (Γ : Env Ty) (τ : Ty) (e0 e1 : Expr) : Type :=
  mk_related_exprs
  { rel_expr_He0 : (TC Γ ⊢ e0 : τ);
    rel_expr_He1 : (TC Γ ⊢ e1 : τ);
    rel_expr_erel {ρ0 ρ1} (Hρ : GREL ρ0, ρ1 ∈ G[Γ]) :
      (E_rel τ
             (mk_config (G_rel_modeling0 Hρ) rel_expr_He0)
             (mk_config (G_rel_modeling1 Hρ) rel_expr_He1))
  }.

Arguments mk_related_exprs {_ _ _ _} _ _ _.


Notation "'EXP' Γ ⊢ e0 ≈ e1 : τ" :=
  (related_exprs Γ τ e0 e1)
    (at level 69, e0 at level 99, e1 at level 99, no associativity).

Definition dirac {A} (v : A) : Meas A :=
  fun e => Indicator e v.

Definition is_dirac {A} (v : A) (m : Meas A) : Prop :=
  m = dirac v.


Ltac decide_eval' ρ exp v w e u :=
  let not_ex := fresh "not_ex" in
  destruct (eval_dec ρ exp) as [[[v w] [e u]] | not_ex];
  [|
   try (contradict not_ex; eexists (_, _); repeat constructor; eassumption);
   try solve [nnr]].
Tactic Notation "decide_eval" uconstr(ρ) "," uconstr(exp) "as"
       "[" ident(v) ident(w) ident(e) ident(u) "]"
  := (decide_eval' ρ exp v w e u).

(* Ltac generalize_inhabit := *)
(*   match goal with *)
(*   | [ |- context[inhabits ?t]] => generalize (inhabits t); intros ?i *)
(*   end. *)

(* Ltac irrelevate_inhabit := *)
(*   match goal with *)
(*     [ H0 : inhabited ?x, H1 : inhabited ?x |- _ ] => *)
(*     pose proof (proof_irrelevance _ H0 H1); subst H0 *)
(*   end. *)

(* Ltac inhabited_irrelevance := progress (repeat generalize_inhabit; repeat irrelevate_inhabit). *)


Axiom int_const_entropy :
  forall (v : R+)
         (f : Entropy -> R+),
     (forall x, f x = v) ->
     Integration f μEntropy = v.

Lemma pure_is_atomic {Γ ρ} {Hρ : ENV ρ ⊨ Γ} {e τ} A
      (Hpure_e : (TC Γ ⊢ e_pure e : τ)) :
  (fun σ => eval_in Hρ Hpure_e A σ) =
  (fun σ => Indicator A (eval_a_wt Hρ Hpure_e)).
Proof.
  extensionality σ.
  unfold eval_in, ev, ew.
  decide_eval Hρ, _ as [v w ex u]; simpl in *. {
    inversion ex; subst.
    nnr.
    unfold nnr_mult.
    simpl.
    rewrite Rmult_1_r.
    (* This is nearly exact copy-paste, needs cleanup *)
    destruct e as [ ? | x ? | x ]; simpl in *. {
      inversion H0.
      unfold eval_a_wt.
      destruct eval_a_preservation.
      subst.
      simpl.
      do 2 f_equal.
      apply WT_Val_eq; simpl.
      inversion e.
      auto.
    } {
      inversion H0.
      unfold eval_a_wt.
      destruct eval_a_preservation.
      subst.
      simpl.
      do 2 f_equal.
      apply WT_Val_eq; simpl.
      inversion e0.
      auto.
    } {
      inversion H0.
      unfold eval_a_wt.
      destruct eval_a_preservation.
      simpl.
      do 2 f_equal.
      apply WT_Val_eq; simpl.
      simpl in *.
      rewrite H1 in e.
      inversion e.
      auto.
    }
  } {
    destruct e as [ ? | x ? | x ]; simpl in *;
try (contradict not_ex; eexists (_, _); constructor; simpl; eauto; fail).

    remember (lookup ρ x).
    destruct o. {
      contradict not_ex; eexists (_, _); constructor; simpl; eauto.
    } {
      unfold eval_a_wt.
      destruct eval_a_preservation.
      contradict e.
      simpl.
      rewrite <- Heqo.
      discriminate.
    }
  }
Qed.

Lemma pure_is_dirac {Γ ρ e τ}
  (Hρ : ENV ρ ⊨ Γ)
  (Hpure_e : TC Γ ⊢ e_pure e : τ) :
  exists v : WT_Val τ,
    eval_a ρ e = Some (projT1 v) /\
    μ Hρ Hpure_e = dirac v.
Proof.
  destruct (eval_a_preservation Hρ Hpure_e).
  exists x.
  split; auto.

  extensionality A.
  unfold μ, dirac; simpl.
  rewrite pure_is_atomic.
  apply int_const_entropy; intro σ.

  f_equal.

  unfold eval_a_wt.
  destruct eval_a_preservation.
  simpl.
  apply WT_Val_eq.
  rewrite e0 in e1.
  inversion e1; subst.
  auto.
Qed.

Lemma compat_real Γ r :
  (EXP Γ ⊢ e_pure (e_real r) ≈ e_pure (e_real r) : ℝ).
Proof.
  refine (mk_related_exprs (TCReal _) (TCReal _) _).
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  pose proof pure_is_dirac (G_rel_modeling0 Hρ) (TCReal r) as H0.
  pose proof pure_is_dirac (G_rel_modeling1 Hρ) (TCReal r) as H1.
  destruct H0 as [v0 [Hea0 Hdirac0]].
  destruct H1 as [v1 [Hea1 Hdirac1]].
  simpl in *.

  rewrite Hdirac0, Hdirac1.

  unfold dirac, Indicator; simpl.
  f_equal.
  apply HA.
  inversion Hea0.
  inversion Hea1.
  subst.
  reflexivity.
Qed.

Lemma compat_var Γ x τ :
  lookup Γ x = Some τ ->
  EXP Γ ⊢ e_pure (e_var x) ≈ e_pure (e_var x) : τ.
Proof.
  intros Γx.
  refine (mk_related_exprs (TCVar _) (TCVar _) _).
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  pose proof pure_is_dirac (G_rel_modeling0 Hρ) (TCVar Γx) as H0.
  pose proof pure_is_dirac (G_rel_modeling1 Hρ) (TCVar Γx) as H1.
  destruct H0 as [v0 [Heval0 Hdirac0]].
  destruct H1 as [v1 [Heval1 Hdirac1]].
  simpl in *.

  rewrite Hdirac0, Hdirac1.

  unfold dirac, Indicator; simpl.
  f_equal.
  apply HA.
  pose proof G_rel_V Hρ Γx Heval0 Heval1.
  eapply G_rel_V; eauto.
Qed.

(* Lemma tcv_of_V_rel {τ v0 v1} : *)
(*   (VREL v0, v1 ∈ V[τ]) -> *)
(*   (TCV ⊢ v0 : τ). *)
(* Proof. *)
(*   intros. *)
(*   destruct τ, v0, v1; simpl in *; try tauto. { *)
(*     constructor. *)
(*   } { *)
(*     destruct H as [[? ?] ?]. *)
(*     repeat subst. *)
(*     econstructor; eauto. *)
(*   } *)
(* Qed. *)


Program
Definition extend_grel {Γ ρ0 ρ1 τ}
           (v0 v1 : WT_Val τ)
           (Hρ : (GREL ρ0, ρ1 ∈ G[Γ]))
           (Hv : VREL (projT1 v0), (projT1 v1) ∈ V[τ])
  : (GREL (extend ρ0 (projT1 v0)), (extend ρ1 (projT1 v1)) ∈ G[extend Γ τ]) :=
  let (Hρ0, Hρ1, Hρ) := Hρ in
  mk_G_rel
    _ _ _
    (env_model_extend Hρ0 v0)
    (env_model_extend Hρ1 v1)
    _.

Next Obligation.
  destruct x. {
    simpl in *.
    inversion H.
    inversion H0.
    inversion H1.
    subst.
    auto.
  } {
    simpl in *.
    eapply Hρ; eauto.
  }
Qed.

Lemma compat_lam Γ body0 body1 τa τr :
  (EXP (extend Γ τa) ⊢ body0 ≈ body1 : τr) ->
  (EXP Γ ⊢ e_pure (e_lam τa body0) ≈ e_pure (e_lam τa body1) : (τa ~> τr)).
Proof.
  intros Hbody.
  destruct Hbody as [Hbody0 Hbody1 Hbodies]; simpl in *.
  refine (mk_related_exprs (TCLam Hbody0) (TCLam Hbody1) _).
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  pose proof pure_is_dirac (G_rel_modeling0 Hρ) (TCLam Hbody0) as H0.
  pose proof pure_is_dirac (G_rel_modeling1 Hρ) (TCLam Hbody1) as H1.
  destruct H0 as [v0 [Heval0 Hdirac0]].
  destruct H1 as [v1 [Heval1 Hdirac1]].
  simpl in *.

  rewrite Hdirac0, Hdirac1.
  unfold dirac, Indicator, widen_event; simpl.
  f_equal.
  apply HA.

  inversion Heval0.
  inversion Heval1.
  subst.

  split; auto.

  exists Γ, (G_rel_modeling0 Hρ), Hbody0.
  exists Γ, (G_rel_modeling1 Hρ), Hbody1.

  intros va0 va1 Hva.
  simpl.
  intros.
  specialize (Hbodies _ _ (extend_grel va0 va1 Hρ Hva) A2 A3 H).
  destruct Hρ; simpl in *.
  apply Hbodies.
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

Lemma tonelli_3 :
  forall {A B} (f : A -> B -> R+) (μx : Meas A) (μy : Meas B),
    Integration (fun x => Integration (fun y => f x y) μy) μx =
    Integration (fun y => Integration (fun x => f x y) μx) μy.
Admitted.

Lemma lemma_1 :
  forall {A B} (f : A -> B -> R+) (μx : Meas A) (μy : Meas B),
    Integration (fun x => Integration (fun y => f x y) μy) μx =
    Integration (fun y => Integration (fun x => f x y) μx) μy.
Proof @tonelli_3.

Definition preimage {A B C} (f : A -> B) : (B -> C) -> (A -> C) :=
  fun eb a => eb (f a).

Lemma lemma_3 :
  forall {X}
         (M : Event X -> Event X -> Prop)
         (μ0 μ1 : Meas X)
         (μs_aggree : forall A0 A1, M A0 A1 -> μ0 A0 = μ1 A1)
         (f0 f1 : X -> R+)
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
  apply μs_aggree.

  specialize (f_is_M_measurable (fun fx => bool_of_dec (fx [>] t))).

  apply f_is_M_measurable.
Qed.

Axiom lemma_9 : forall (g : Entropy -> Entropy -> R+),
    Integration (fun σ => g (πL σ) (πR σ)) μEntropy =
    Integration (fun σL => Integration (fun σR => g σL σR) μEntropy) μEntropy.

Lemma pick_3_and_waste : forall (g : Entropy -> Entropy -> Entropy -> Entropy -> R+),
    Integration (fun σ => g (π 0 σ) (π 1 σ) (π 2 σ) (πR (πR (πR σ)))) μEntropy =
    Integration
      (fun σ0 =>
         Integration
           (fun σ1 =>
              Integration
                (fun σ2 =>
                   Integration
                     (fun σ3 =>
                        g σ0 σ1 σ2 σ3)
                     μEntropy)
                μEntropy)
           μEntropy)
      μEntropy.
Proof.
  intros.

  evar (x : Entropy -> R+).
  replace (Integration (fun σ0 => Integration _ _) _)
  with (Integration x μEntropy).
  shelve. {
    integrand_extensionality σ0.

    evar (y : Entropy -> R+).
    replace (Integration _ _)
    with (Integration y μEntropy).
    shelve. {
      integrand_extensionality σ1.

      rewrite <- lemma_9.
      subst y.
      reflexivity.
    }
    Unshelve.
    shelve.
    shelve.
    subst y.
    rewrite <- lemma_9.
    subst x.
    reflexivity.
  }
  Unshelve.
  subst x.
  rewrite <- lemma_9.
  simpl.
  auto.
Qed.

Lemma pick_3_entropies : forall (g : Entropy -> Entropy -> Entropy -> R+),
    Integration (fun σ => g (π 0 σ) (π 1 σ) (π 2 σ)) μEntropy =
    Integration
      (fun σ0 =>
         Integration
           (fun σ1 =>
              Integration
                (fun σ2 =>
                   g σ0 σ1 σ2)
                μEntropy)
           μEntropy)
      μEntropy.
Proof.
  intros.
  pose proof pick_3_and_waste (fun (σ0 σ1 σ2 σR : Entropy) => g σ0 σ1 σ2).
  simpl in *.
  rewrite H.

  integrand_extensionality σ0.
  integrand_extensionality σ1.
  integrand_extensionality σ2.
  erewrite int_const_entropy; auto.
Qed.

Lemma pick_2_entropies : forall (g : Entropy -> Entropy -> R+),
    Integration (fun σ => g (π 0 σ) (π 1 σ)) μEntropy =
    Integration (fun σ0 => Integration (fun σ1 => g σ0 σ1) μEntropy) μEntropy.
Proof.
  intros.
  pose proof pick_3_entropies (fun (σ0 σ1 σ2 : Entropy) => g σ0 σ1).
  simpl in *.
  rewrite H.

  integrand_extensionality σ0.
  integrand_extensionality σ1.
  erewrite int_const_entropy; auto.
Qed.

Theorem theorem_15 :
  forall {Γ e τ ρ}
    (He : TC Γ ⊢ e : τ)
    (Hρ : ENV ρ ⊨ Γ)
    (f : WT_Val τ -> R+),
      Integration f (μ Hρ He) =
      Integration (fun σ => option0 (f <$> ev Hρ He σ) [*] ew Hρ He σ) μEntropy.
Proof.
  intros Γ e τ ρ He Hρ f.

  unfold μ.

  rewrite riemann_def_of_lebesgue_integration.
  rewrite lemma_1.
  unfold eval_in.

  match goal with
  | [ |- _ (fun y => _ (fun x => ?v [*] ?w) _) _ = _ ] =>
    assert ((fun y : Entropy => Integration (fun x => v [*] w) lebesgue_measure) =
            (fun y : Entropy => Integration (fun x => v) lebesgue_measure [*] w))
  end.
  {
    extensionality σ.
    rewrite <- Integration_linear_mult_r.
    auto.
  }
  rewrite H.
  clear H.

  f_equal.
  extensionality σ.

  generalize (ew Hρ He σ) as w, (ev Hρ He σ) as v.
  intros.

  f_equal.
  induction v; simpl. {
    pose proof @integration_of_indicator.
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

Definition ensemble_of_event {X} : Event X -> Ensemble X :=
  fun A x => A x = true.

Definition at_most_one {A} (P : A -> Prop) :=
  forall x, P x -> (forall x', P x' -> x = x').

Lemma option_map_compose {A B C} (f : B -> C) (g : A -> B) (o : option A) :
  f <$> (g <$> o) = (f ∘ g) <$> o.
Proof.
  destruct o; reflexivity.
Qed.

Definition plus_in (A : Event (WT_Val ℝ)) (v v' : WT_Val ℝ) : R+ :=
  match (projT1 v), (projT1 v') with
  | v_real r, v_real r' =>
    Indicator A (existT _ (v_real (r + r')) (TCVReal _))
  | _, _ => nnr_0
  end.

Lemma by_theorem_15_plus {ρ el er Γ} A
  (Hel : TC Γ ⊢ el : ℝ)
  (Her : TC Γ ⊢ er : ℝ)
  (Hρ : ENV ρ ⊨ Γ) :
    Integration (fun σ => eval_in Hρ (TCPlus Hel Her) A σ) μEntropy =
    Integration (fun vl =>
    Integration (fun vr =>
                   plus_in A vl vr
                ) (μ Hρ Her)
                ) (μ Hρ Hel).
Proof.
  setoid_rewrite theorem_15; eauto.
  setoid_rewrite theorem_15; eauto.

  replace (Integration _ μEntropy)
  with (Integration
          (fun σ0 =>
             Integration
               (fun σ1 =>
                  option0 (plus_in A <$> ev Hρ Hel σ0 <*> ev Hρ Her σ1)
                          [*] (ew Hρ Her σ1))
               μEntropy
               [*] (ew Hρ Hel σ0))
          μEntropy). {
    f_equal.
    extensionality σ0.
    f_equal.
    unfold option_map, plus_in, ew, ev.
    decide_eval Hρ, Hel as [v0 w0 ex0 u0]; simpl; auto.
    rewrite <- Integration_linear_mult_l.
    nnr.
  } {
    evar (x : Entropy -> Entropy -> R+).
    replace (fun σ => eval_in Hρ (TCPlus Hel Her) A σ)
    with (fun σ => x (π 0 σ) (π 1 σ)); subst x. {
      rewrite pick_2_entropies.
      setoid_rewrite Integration_linear_mult_r at 1.
      reflexivity.
    } {
      extensionality σ.
      unfold eval_in, ew, ev.
      decide_eval Hρ, (TCPlus _ _) as [v0 w0 ex0 u0]; simpl. {
        inversion ex0; subst.
        decide_eval Hρ, Hel as [v3 w3 ex3 u3]; simpl.
        decide_eval Hρ, Her as [v4 w4 ex4 u4]; simpl.

        specialize (u3 (_, _) X).
        specialize (u4 (_, _) X0).
        inversion u3; subst.
        inversion u4; subst.

        unfold plus_in; simpl.

        setoid_rewrite <- (tcv_highlander (TCVReal (r0 + r1))).
        nnr.
      } {
        decide_eval Hρ, Hel as [v3 w3 ex3 u3].
        decide_eval Hρ, Her as [v4 w4 ex4 u4].
        destruct v3, v4; try nnr.
        contradict not_ex.
        eexists (_, _).
        constructor; eauto.
      }
    }
  }
Qed.

Definition the_other_A_rel (τ : Ty) (A0 A1 : Event (WT_Val τ)) :=
  forall v0 v1 (Hv : V_rel τ (projT1 v0) (projT1 v1)),
    (A0 v0 = (* iff *) A1 v1).

Print eq_rect.

Definition narrow_event {τ} (A : Event (WT_Val τ)) : Event Val :=
  fun v =>
    match decidable_tcv v with
    | inl (existT _ τ' tc) =>
      match ty_eq_dec τ' τ with
      | left Heq => A (existT _ v (rew Heq in tc))
      | right _ => false
      end
    | inr _ => false
    end.

Lemma narrow_widen_inverse τ (A : Event (WT_Val τ)) : widen_event (narrow_event A) = A.
Proof.
  extensionality v.
  destruct v.
  unfold widen_event, narrow_event.
  simpl.
  destruct decidable_tcv as [[]|]. {
    destruct ty_eq_dec. {
      subst.
      do 2 f_equal.
      compute.
      eapply tcv_highlander.
    } {
      pose proof (vtype_highlander t t0).
      contradict n; auto.
    }
  } {
    contradict n.
    repeat econstructor; eauto.
  }
Qed.

Lemma V_rel_implies_TCV {τ v0 v1} :
  V_rel τ v0 v1 ->
  inhabited (TCV ⊢ v0 : τ) /\ inhabited (TCV ⊢ v1 : τ).
Proof.
  intros.
  induction τ, v0, v1; split; try contradiction H; try (repeat constructor; fail). {
    destruct H as [? [Γ_clo0 [Hρ_clo0 [tc_body0 [Γ_clo1 [Hρ_clo1 [tc_body1 _]]]]]]].
    inversion p; subst.
    constructor.
    econstructor; eauto.
  } {
    destruct H as [? [Γ_clo0 [Hρ_clo0 [tc_body0 [Γ_clo1 [Hρ_clo1 [tc_body1 _]]]]]]].
    inversion p.
    do 2 subst.
    constructor.
    econstructor; eauto.
  }
Qed.

Lemma convert_A_rel :
  forall {Γ e0 e1 τ}
  {He0 : TC Γ ⊢ e0 : τ}
  {He1 : TC Γ ⊢ e1 : τ}
  {ρ0 ρ1 : Env Val}
  {Hρ : GREL ρ0, ρ1 ∈ G[ Γ]},
    (forall A0 A1 : Event Val,
        A_rel τ A0 A1 ->
        μ (G_rel_modeling0 Hρ) He0 (widen_event A0) =
        μ (G_rel_modeling1 Hρ) He1 (widen_event A1)) ->
    (forall A0 A1 : Event (WT_Val τ),
        the_other_A_rel τ A0 A1 ->
        μ (G_rel_modeling0 Hρ) He0 A0 =
        μ (G_rel_modeling1 Hρ) He1 A1).
Proof.
  intros.
  specialize (H (narrow_event A0) (narrow_event A1)).
  repeat rewrite narrow_widen_inverse in *.
  apply H.
  clear H.
  intros v0 v1 Hv.
  unfold narrow_event.
  repeat destruct decidable_tcv; auto. {
    destruct s, s0.
    repeat destruct ty_eq_dec; subst; auto. {
      apply False_rect.
      destruct (V_rel_implies_TCV Hv) as [[] []].
      pose proof (vtype_highlander t0 X0).
      contradiction.
    } {
      apply False_rect.
      destruct (V_rel_implies_TCV Hv) as [[] []].
      pose proof (vtype_highlander t X).
      contradiction.
    }
  } {
    apply False_rect.
    destruct (V_rel_implies_TCV Hv) as [[] []].
    apply n.
    repeat econstructor; eauto.

  } {
    apply False_rect.
    destruct (V_rel_implies_TCV Hv) as [[] []].
    apply n.
    repeat econstructor; eauto.
  }
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
  intros A0 A1 HA.

  specialize (Hl _ _ Hρ).
  specialize (Hr _ _ Hρ).

  unfold μ.

  do 2 rewrite by_theorem_15_plus.

  pose proof convert_A_rel Hl as Hl'.
  pose proof convert_A_rel Hr as Hr'.

  apply (lemma_3 (the_other_A_rel ℝ)); intuition.
  intros vl0 vl1 Hvl.
  unfold preimage.
  f_equal.

  apply (lemma_3 (the_other_A_rel ℝ)); intuition.
  intros vr0 vr1 Hvr.
  unfold preimage.
  f_equal.

  destruct vl0 as [[|]], vl1 as [[|]], vr0 as [[|]], vr1 as [[|]]; try contradiction.

  simpl in *.

  inversion Hvl.
  inversion Hvr.
  subst.

  unfold plus_in; simpl.
  unfold Indicator.
  f_equal.
  apply HA.
  simpl.
  auto.
Qed.

(* Ltac pull_from_tcv_dont_care := *)
(*   progress repeat *)
(*   match goal with *)
(*   | [ |- context[ pull_from_inhabited_tcv ?i ] ] => *)
(*     generalize (pull_from_inhabited_tcv i); clear i; intro *)
(*   end. *)

Lemma apply_in_absurd {τa τr} (τeq : ℝ = τa ~> τr) : False.
Proof.
  inversion τeq.
Qed.

Lemma apply_in_convert_τa {τa τr τa0 τr0} (τeq : (τa0 ~> τr0) = (τa ~> τr))
  : τa = τa0.
Proof.
  inversion τeq; subst; auto.
Qed.

Lemma apply_in_convert_τr {τa τr τa0 τr0} (τeq : (τa0 ~> τr0) = (τa ~> τr))
  : τr = τr0.
Proof.
  inversion τeq; subst; auto.
Qed.

Definition apply_in_convert_Hbody
      {τa τr τa0 τr0 Γ_clo body}
      (Hbody : TC (extend Γ_clo τa0) ⊢ body : τr0)
      (τeq : (τa0 ~> τr0) = (τa ~> τr)) :
    (TC (extend Γ_clo τa) ⊢ body : τr).
Proof.
  inversion τeq; subst; auto.
Defined.

Definition apply_in {τa τr} (A : Event (WT_Val τr)) (σ : Entropy)
        (vf : WT_Val (τa ~> τr))
        (va : WT_Val τa)
  : R+ :=
  match projT2 vf in (TCV ⊢ vf : τf) return (τf = τa ~> τr -> R+) with
  | @TCVClo body Γ_clo τa0 τr0 ρ_clo Hρ Hbody =>
    fun τeq =>
      (eval_in
         (env_model_extend Hρ va)
         (apply_in_convert_Hbody Hbody τeq)
         A
         σ)
  | _ => fun τeq => False_rect _ (apply_in_absurd τeq)
  end eq_refl.

Lemma elim_apply_in {τa τr} (A : Event (WT_Val τr)) (σ : Entropy)
      {Γ ρ} (Hρ : ENV ρ ⊨ Γ)
      (body : Expr)
      (tc_body : TC (extend Γ τa) ⊢ body : τr)
      {va : WT_Val τa}
  : eval_in (env_model_extend Hρ va) tc_body A σ =
    apply_in A σ (existT _ (v_clo τa body ρ) (TCVClo Hρ tc_body)) va.
Proof.
  simpl in *.
  unfold apply_in; simpl.
  f_equal.
Qed.

Lemma by_theorem_15_app {ρ ef ea Γ τa τr} A
  (Hef : TC Γ ⊢ ef : (τa ~> τr))
  (Hea : TC Γ ⊢ ea : τa)
  (Hρ : ENV ρ ⊨ Γ) :
    Integration (fun σ => eval_in Hρ (TCApp Hef Hea) A σ) μEntropy =
    Integration (fun vf =>
    Integration (fun va =>
    Integration (fun σ2 =>
                   apply_in A σ2 vf va
                ) μEntropy
                ) (μ Hρ Hea)
                ) (μ Hρ Hef).
Proof.
  setoid_rewrite theorem_15; eauto.
  setoid_rewrite theorem_15; eauto.

  replace (Integration _ μEntropy)
  with (Integration
          (fun σ0 =>
             Integration
               (fun σ1 =>
                  Integration
                    (fun σ2 =>
                       option0 (apply_in A σ2 <$> ev Hρ Hef σ0 <*> ev Hρ Hea σ1))
                    μEntropy
                    [*] ew Hρ Hea σ1)
               μEntropy
               [*] ew Hρ Hef σ0)
          μEntropy). {
    f_equal.
    extensionality σ0.
    f_equal.
    unfold option_map, ew, ev.
    decide_eval Hρ, Hef as [v0 w0 ex0 u0]; simpl. {
      f_equal.
      extensionality σ1.
      decide_eval Hρ, Hea as [v1 w1 ex1 u1]; simpl; auto.
    } {
      rewrite <- Integration_linear_mult_l.
      erewrite int_const_entropy; auto.
      nnr.
    }
  } {
    evar (x : Entropy -> Entropy -> Entropy -> R+).
    replace (fun σ => eval_in Hρ (TCApp Hef Hea) A σ)
    with (fun σ => x (π 0 σ) (π 1 σ) (π 2 σ)); subst x. {
      rewrite pick_3_entropies.
      f_equal.
      extensionality σ0.
      rewrite Integration_linear_mult_r.
      f_equal.
      extensionality σ1.
      rewrite 2 Integration_linear_mult_r.
      f_equal.
      reflexivity.
    } {
      extensionality σ.
      unfold eval_in, ev, ew.
      decide_eval Hρ, (TCApp _ _) as [v0 w0 ex0 u0]; simpl. {
        inversion ex0; subst.
        decide_eval Hρ, Hef as [v4 w4 ex4 u4]; simpl.
        decide_eval Hρ, Hea as [v5 w5 ex5 u5]; simpl.

        unfold apply_in.
        simpl.

        generalize (@apply_in_absurd τa τr).
        generalize (@apply_in_convert_Hbody τa τr).
        generalize (@apply_in_convert_τa τa τr).
        generalize (@apply_in_convert_τr τa τr).
        intros.
        destruct big_preservation. {
          apply False_rect.
          apply f; auto; econstructor; eauto.
        }

        specialize (H _ _ eq_refl).
        specialize (H0 _ _ eq_refl).
        subst τa1 τr0.

        specialize (u4 (_, _) X).
        specialize (u5 (_, _) X0).
        inversion u4; subst.
        inversion u5; subst.

        unfold eval_in, ev, ew.

        set (Hρ' := env_model_extend _ _).
        decide_eval Hρ', _ as [v6 w6 ex6 u6]. {
          simpl.

          do 2 set (existT _ _ _).

          specialize (u6 (v0, w3) X1).
          inversion u6; subst.
          enough (s = s0) by (rewrite H; nnr).
          subst s s0.
          apply WT_Val_eq.
          simpl.
          auto.
        }
      } {
        decide_eval Hρ, Hef as [v3 w3 ex3 u3].
        decide_eval Hρ, Hea as [v4 w4 ex4 u4].
        destruct v3 as [|x body ρ_clo]. {
          simpl.
          set (big_preservation _ _ _ _).
          inversion t.
        } {
          simpl.
          unfold apply_in, eval_in, ev, ew; simpl.

          generalize (@apply_in_absurd τa τr).
          generalize (@apply_in_convert_Hbody τa τr).
          generalize (@apply_in_convert_τa τa τr).
          generalize (@apply_in_convert_τr τa τr).
          intros.
          destruct big_preservation. {
            apply False_rect.
            apply f; auto; econstructor; eauto.
          }

          set (env_model_extend _ _).
          decide_eval t2, _ as [v5 w5 ex5 u5].
          contradict not_ex.
          eexists (_, _).
          econstructor; eauto.
        }
      }
    }
  }
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
  intros A0 A1 HA.

  specialize (Hf _ _ Hρ).
  specialize (Ha _ _ Hρ).

  unfold μ.

  do 2 rewrite by_theorem_15_app.


  pose proof convert_A_rel Hf as Hf'.
  pose proof convert_A_rel Ha as Ha'.

  apply (lemma_3 (the_other_A_rel (τa ~> τr))); intuition.
  intros vf0 vf1 Hvf.
  unfold preimage.
  f_equal.

  apply (lemma_3 (the_other_A_rel τa)); intuition.
  intros va0 va1 Hva.
  unfold preimage.
  f_equal.

  destruct vf0 as [[|x0 body0 ρ_clo0]]; try contradiction.
  destruct vf1 as [[|x1 body1 ρ_clo1]]; try contradiction.

  (* destruct i. *)
  (* inversion t; subst. *)
  (* rename Γ_clo into Γ_clo0, X into Hρ_clo0, X0 into Hbody0. *)
  (* assert (Hρ_clo0' : ENV (extend ρ_clo0 x0 va0) ⊨ (extend Γ_clo0 x0 τa)). { *)
  (*   apply env_model_extend; auto. *)
  (*   apply pull_from_inhabited_tcv. *)
  (*   auto. *)
  (* } *)

  (* destruct i0. *)
  (* inversion t0; subst. *)
  (* rename Γ_clo into Γ_clo1, X into Hρ_clo1, X0 into Hbody1. *)
  (* assert (Hρ_clo1' : ENV (extend ρ_clo1 x1 va1) ⊨ (extend Γ_clo1 x1 τa)). { *)
  (*   apply env_model_extend; auto. *)
  (*   apply pull_from_inhabited_tcv. *)
  (*   auto. *)
  (* } *)

  destruct Hvf as [? [Γ_clo0 [Hρ_clo0 [tc_body0 [Γ_clo1 [Hρ_clo1 [tc_body1 Hvf]]]]]]].
  inversion p; repeat subst.
  simpl in *.
  specialize (Hvf va0 va1 Hva A0 A1 HA).

  unfold μ in Hvf.

  (* assert (@eq (WT_Val τa) (exist va0 Hva0) (exist va0 (inhabits Hva0'))). { *)
  (*   f_equal. *)
  (*   apply proof_irrelevance. *)
  (* } *)
  (* setoid_rewrite H. *)
  (* clear H Hva0. *)
  (* assert (@eq (WT_Val τa) (exist va1 Hva1) (exist va1 (inhabits Hva1'))). { *)
  (*   f_equal. *)
  (*   apply proof_irrelevance. *)
  (* } *)
  (* setoid_rewrite H. *)
  (* clear H Hva1. *)


  rewrite (tcv_highlander t (TCVClo Hρ_clo0 tc_body0)).
  rewrite (tcv_highlander t0 (TCVClo Hρ_clo1 tc_body1)).
  setoid_rewrite <- elim_apply_in.
  apply Hvf.
Qed.

Lemma compat_sample Γ :
  EXP Γ ⊢ e_sample ≈ e_sample : ℝ.
Proof.
  refine (mk_related_exprs TCSample TCSample _).
  simpl.
  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  unfold μ.
  f_equal.
  extensionality σ.

  pose proof ESample ρ0 σ as EVAL_0.
  pose proof ESample ρ1 σ as EVAL_1.

  unfold eval_in, ev, ew.

  decide_eval (G_rel_modeling0 Hρ), _ as [v0 w0 e0 u0].
  decide_eval (G_rel_modeling1 Hρ), _ as [v1 w1 e1 u1].
  injection (u0 (_, _) EVAL_0); intros.
  injection (u1 (_, _) EVAL_1); intros.
  subst.

  simpl.
  unfold Indicator.
  do 2 f_equal.
  apply HA.
  simpl.
  reflexivity.
Qed.

Definition factor_in (A : Event (WT_Val ℝ)) (v : WT_Val ℝ) : R+ :=
  match projT1 v with
  | v_real r =>
    match Rle_dec 0 r with
    | left rpos => Indicator A (existT _ (v_real r) (TCVReal _)) [*] mknnr r rpos
    | _ => nnr_0
    end
  | _ => nnr_0
  end.

Lemma by_theorem_15_factor {ρ e Γ} A
      (He : (TC Γ ⊢ e : ℝ))
      (Hρ : ENV ρ ⊨ Γ) :
  Integration (fun σ => eval_in Hρ (TCFactor He) A σ) μEntropy =
    Integration (factor_in A) (μ Hρ He).
Proof.
  setoid_rewrite theorem_15; eauto.

  integrand_extensionality σ.
  unfold option_map, factor_in, eval_in, ev, ew.

  decide_eval Hρ, _ as [v0 w0 ex0 u0]. {
    inversion ex0.
    subst.
    decide_eval Hρ, _ as [v1 w1 ex1 u1]. {
      simpl.
      injection (u1 (_, _) X); intros.
      subst.
      destruct Rle_dec. {
        do 2 set (existT _ _ _).
        rewrite (@WT_Val_eq _ s s0); [nnr |].
        subst s s0.
        simpl.
        auto.
      } {
        contradict n; auto.
      }
    }
  } {
    simpl.
    decide_eval Hρ, _ as [v1 w1 ex1 u1].
    simpl.
    destruct v1; try solve [nnr].
    destruct Rle_dec; try solve [nnr].

    contradict not_ex.
    eexists (v_real r, _).
    eapply EFactor with (rpos := r0).
    eauto.
  }
Qed.

Lemma compat_factor Γ e0 e1:
  (EXP Γ ⊢ e0 ≈ e1 : ℝ) ->
  (EXP Γ ⊢ e_factor e0 ≈ e_factor e1 : ℝ).
Proof.
  intro He.
  destruct He as [TC0 TC1 He].
  refine (mk_related_exprs (TCFactor _) (TCFactor _) _).
  simpl in *.

  intros ρ0 ρ1 Hρ.
  intros A0 A1 HA.

  specialize (He _ _ Hρ).

  unfold μ.

  rewrite (by_theorem_15_factor _ TC0 (G_rel_modeling0 Hρ)).
  rewrite (by_theorem_15_factor _ TC1 (G_rel_modeling1 Hρ)).

  pose proof convert_A_rel He as He'.

  apply (lemma_3 (the_other_A_rel ℝ)); intuition.
  intros v0 v1 Hv.
  unfold preimage.
  f_equal.

  destruct v0 as [? ?], v1 as [? ?].
  unfold factor_in.
  simpl.

  inversion t.
  inversion t0.
  subst.

  simpl in Hv.
  inversion Hv.
  subst.

  destruct Rle_dec; auto.
  unfold Indicator.
  do 2 f_equal.
  apply HA.
  simpl.
  auto.
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

SearchAbout WT_Val.

Print Val_rect.

Lemma WT_Val_rect
        (P : forall τ v, (TCV ⊢ v : τ) -> Type)
        (case_real :
           forall r tc,
             P ℝ (v_real r) tc)
        (case_clo :
           forall τa τr body ρ tc Γ,
             ENV ρ ⊨ Γ ->
             (forall x τ v,
                 lookup Γ x = Some τ ->
                 lookup ρ x = Some v ->
                 existsT Hv, P τ v Hv) ->
             P (τa ~> τr) (v_clo τa body ρ) tc)
  : forall τ v Hv, P τ v Hv.
Proof.
  intros.
  Check tc_val_env_rect.
  induction Hv using tc_val_env_rect
  with
  (P := fun v τ Hv => P τ v Hv)
    (P0 := fun ρ Γ Hρ =>
             forall x τ v
                    (Γx : lookup Γ x = Some τ)
                    (ρx : lookup ρ x = Some v),
               P τ v (lookup_tc_env Hρ Γx ρx)). {
    apply case_real.
  } {
    apply case_clo with (Γ := Γ_clo); auto.
    intros.
    eexists.
    apply (IHHv x τ v H H0).
  } {
    intros.
    destruct x; discriminate Γx.
  } {
    intros.

    destruct x; intros. {
      simpl in *.
      inversion Γx.
      inversion ρx.
      subst.
      rewrite <- (tcv_highlander Hv).
      auto.
    } {
      simpl in Γx, ρx.
      specialize (IHHv _ _ _ Γx ρx).
      rewrite <- (tcv_highlander (lookup_tc_env t Γx ρx)).
      auto.
    }
  }
Qed.

Lemma tc_nil_clo_body {τa τr body ρ} :
  ρ = nil ->
  (TCV ⊢ v_clo τa body ρ : τa ~> τr) ->
  (TC extend nil τa ⊢ body : τr).
Proof.
  intros.
  subst.
  inversion X.
  inversion X0.
  subst.
  auto.
Qed.

(* Lemma append_models {Γ0 Γ1 ρ0 ρ1} : *)
(*   ENV ρ0 ⊨ Γ0 -> *)
(*   ENV ρ1 ⊨ Γ1 -> *)
(*   ENV ρ0 ++ ρ1 ⊨ Γ0 ++ Γ1. *)
(* Proof. *)
(*   intros. *)
(*   induction X; auto. *)
(*   simpl. *)
(*   constructor; auto. *)
(* Qed. *)

(* Lemma reverse_models {Γ ρ} : *)
(*   ENV ρ ⊨ Γ -> *)
(*   ENV rev ρ ⊨ rev Γ. *)
(* Proof. *)
(*   intros. *)
(*   induction X. { *)
(*     constructor. *)
(*   } { *)
(*     simpl. *)
(*     apply append_models; auto. *)
(*     repeat constructor; auto. *)
(*   } *)
(* Qed. *)


Fixpoint close_expr {Γ ρ} (Hρ : ENV ρ ⊨ Γ) (e : Expr) : Expr :=
  match Hρ with
  | TCENil => e
  | @TCECons _ τ _ _ Hρ' Hv =>
    close_expr Hρ' (e_app (e_pure (e_lam τ e)) (expr_of_val' Hv))
  end
with
expr_of_val' {τ v} (Hv : (TCV ⊢ v : τ)) : Expr :=
  match Hv with
  | TCVReal r => e_pure (e_real r)
  | @TCVClo body _ τa _ _ Hρ Hbody =>
    close_expr Hρ (e_pure (e_lam τa body))
  end.

(* Lemma foo1 {Γ ρ} (Hρ : ENV ρ ⊨ Γ) {v τ} (Hv : TCV ⊢ v : τ) e τr : *)
(*   TC (τ :: Γ) ⊢ close_expr Hρ e : τr -> *)
(*   TC Γ ⊢ close_expr (TCECons Hρ Hv) e : τr. *)
(* Proof. *)
(* Admitted. *)

(* Lemma foo2 {Γ ρ} (Hρ : ENV ρ ⊨ Γ) {v τ} (Hv : TCV ⊢ v : τ) e τr : *)
(*   TC Γ ⊢ close_expr (TCECons Hρ Hv) e : τr -> *)
(*   TC (τ :: Γ) ⊢ close_expr Hρ e : τr. *)
(* Proof. *)
(*   intros. *)
(*   induction Hρ. { *)
(*     simpl. *)
(*     simpl in H. *)
(*     inversion H; subst. *)
(*     inversion H2; subst. *)
(*     apply H1. *)
(*   } *)
(* Admitted. *)

(* Lemma expr_of_val {τ v} (Hv : (TCV ⊢ v : τ)) : *)
(*   (TC nil ⊢ expr_of_val' Hv : τ). *)
(* Proof. *)
(*   destruct Hv; try constructor. *)
(*   simpl. *)

(*   (* replace Γ_clo with ([] ++ Γ_clo) in * by trivial. *) *)
(*   (* set (Γ := nil) in *. *) *)
(*   (* clearbody Γ. *) *)
(*   (* revert Γ t0. *) *)

(*   induction t; intros. { *)
(*     simpl. *)
(*     constructor. *)
(*     (* rewrite app_nil_r in t0. *) *)
(*     auto. *)
(*   } { *)
(*     apply foo1. *)
(*     pose proof foo1 t t1. *)


(* Qed. *)

(* Lemma expr_of_val_wt_ex {v τ} (Hv : (TCV ⊢ v : τ)) : *)
(*   {e : Expr & expr_of_val' v = Some e}. *)
(* Proof. *)
(*   induction Hv using tc_val_env_rect *)
(*   with (P0 := fun ρ Γ Hρ => *)
(*                 forall x v τ, *)
(*                   lookup Γ x = Some τ -> *)
(*                   lookup ρ x = Some v -> *)
(*                   {e : Expr & expr_of_val' v = Some e}). { *)
(*     eexists. *)
(*     reflexivity. *)
(*   } { *)
(*     induction t; intros. { *)
(*       eexists. *)
(*       reflexivity. *)
(*     } { *)
(*       eexists. *)
(*       simpl. *)
(*       destruct decidable_tcv as [[?τ Hv]|]. { *)
(*         assert (τ0 = τ) by (eapply vtype_highlander; eauto). *)
(*         subst. *)
(*         destruct IHt. *)
(*       } { *)
(*         contradict n. *)
(*         exists τ. *)
(*         auto. *)
(*       } *)
(*     } *)
(*   } *)
(* Qed. *)

Lemma fundamental_property_of_values v τ :
  (TCV ⊢ v : τ) ->
  (VREL v, v ∈ V[τ]).
Proof.
  intros.
  destruct X using tc_val_env_rect
  with (P0 := fun ρ Γ Hρ => GREL ρ, ρ ∈ G[Γ]). {
    reflexivity.
  } {
    simpl.
    split; auto.

    exists Γ_clo.
    exists t.
    exists t0.
    exists Γ_clo.
    exists t.
    exists t0.
    intros ? ? Hva ? ? HA.

    pose proof fundamental_property t0.
    destruct H as [He He0 H].
    simpl in H.
    specialize (H _ _ (extend_grel va0 va1 IHX Hva)).
    specialize (H A0 A1 HA).
    assert (He = t0) by apply tc_highlander.
    assert (He0 = t0) by apply tc_highlander.
    subst.
    replace (G_rel_modeling0 _) with (env_model_extend t va0)
      in H by apply tc_env_highlander.
    replace (G_rel_modeling1 _) with (env_model_extend t va1)
      in H by apply tc_env_highlander.
    exact H.
  } {
    repeat constructor.
    intros.
    destruct x; inversion H.
  } {
    repeat constructor; auto.
    intros.
    destruct x. {
      simpl in *.
      inversion H.
      inversion H0.
      inversion H1.
      subst τ0 v0 v1.
      auto.
    } {
      simpl in *.
      eapply (G_rel_V IHX); eauto.
    }
  }
Qed.
