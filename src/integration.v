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

Definition Event X := X -> bool.

Definition Meas A := (Event A -> R+).


(* ifte is a function version of "if then else" so that f_equal can deal with it *)
Definition ifte {X} (a : bool) (b c : X) := if a then b else c.
Definition indicator {X} (b : Event X) : X -> R+ := fun x => ifte (b x) 1 0.

Definition full_event {X} : Event X := const true.

Axiom μEntropy : Meas Entropy.
Axiom μEntropy_is_a_probability_measure : μEntropy full_event = 1.

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

Lemma int_const_entropy :
  forall (v : R+)
         (f : Entropy -> R+),
    (forall x, f x = v) ->
    integration f μEntropy = v.
Proof.
  intros.
  replace f with (fun x => f x * 1) by (extensionality x; ring).
  setoid_rewrite H.
  rewrite <- integration_linear_mult_l.
  replace (fun _ => _) with (@indicator Entropy full_event) by auto.
  rewrite integration_of_indicator.
  rewrite μEntropy_is_a_probability_measure.
  ring.
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