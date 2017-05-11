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
  match goal with
  | [ |- _ = _ :> R+ ] => idtac
  | [ |- _ = _ :> Meas _ ] => let A := fresh "A" in extensionality A
  | [ |- _ = _ :> _ -> R+ ] => let A := fresh "A" in extensionality A
  end;
  refine (f_equal2 integration _ eq_refl);
  extensionality x.

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

Axiom lebesgue_measure : Meas R.
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

Definition lebesgue_01_ivl : Meas R :=
  fun A => lebesgue_measure (fun r =>
                               if Rle_dec 0 r
                               then if Rle_dec r 1
                                    then A r
                                    else false
                               else false).


Definition meas_bind {A B} (μ : Meas A) (f : A -> Meas B) : Meas B :=
  fun ev => integration (fun a => f a ev) μ.
Infix ">>=" := meas_bind (at level 20).

Definition fold_bind {A B} (μ : Meas A) (f : A -> Meas B) V :
  integration (fun a => f a V) μ = (μ >>= f) V := eq_refl.

Definition empty_meas A : Meas A := fun a => 0.
Arguments empty_meas _ _ /.

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
| leb_finite : SigmaFinite lebesgue_measure
| leb_pos_finite : SigmaFinite lebesgue_pos_measure.
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
Arguments preimage {_ _ _} _ _ _ /.

Definition pushforward {A B} (μ : Meas A) (f : A -> B) : Meas B :=
  μ ∘ preimage f.

(** two different ways to convert emptiness in an option to emptiness in a
    measure. *)
Definition option_meas {A} (oμ : option (Meas A)) : Meas A :=
  fromOption (empty_meas _) oμ.

Definition meas_option {A} (μo : Meas (option A)) : Meas A :=
  fun ev => μo (fun oa =>
                  match oa with
                  | Some x => ev x
                  | _ => false
                  end).

Axiom μEntropy_proj_is_lebesgue : forall n : nat,
    pushforward μEntropy (fun σ => proj1_sig (σ n)) = lebesgue_01_ivl.

Lemma pushforward_compose {A B C} μ (f : B -> C) (g : A -> B) :
  pushforward μ (f ∘ g) = pushforward (pushforward μ g) f.
Proof.
  trivial.
Qed.

Lemma integration_of_pushforward {A B} (g : A -> B) f μ :
  integration f (pushforward μ g) = integration (f ∘ g) μ.
Proof.
  intros.
  setoid_rewrite riemann_def_of_lebesgue_integration.
  unfold pushforward, preimage, compose.
  trivial.
Qed.

Lemma bind_of_pushforward {A B C} (g : A -> B) (f : B -> Meas C) μ :
  (pushforward μ g) >>= f = μ >>= (f ∘ g).
Proof.
  extensionality ev.
  unfold ">>=".
  rewrite integration_of_pushforward.
  auto.
Qed.

Lemma pushforward_as_bind {A B} μ (f : A -> B) :
  pushforward μ f = μ >>= (dirac ∘ f).
Proof.
  rewrite <- meas_id_right at 1.
  apply bind_of_pushforward.
Qed.

Lemma integration_of_0 :
  forall {A} (μ : Meas A),
    integration (fun _ => 0) μ = 0.
Proof.
  intros.
  replace 0 with (0 * 0) by ring.
  rewrite <- integration_linear_mult_r.
  ring.
Qed.

Lemma bind_empty {A B} f :
  empty_meas A >>= f = empty_meas B.
Proof.
  extensionality ev.
  setoid_rewrite riemann_def_of_lebesgue_integration.
  unfold empty_meas.
  apply integration_of_0.
Qed.

Lemma integration_linear_in_meas {A B} (μ : Meas A) (s : R+) (f : A -> Meas B) :
  (fun ev => s * μ ev) >>= f =
  (fun ev => s * (μ >>= f) ev).
Proof.
  extensionality ev.
  setoid_rewrite riemann_def_of_lebesgue_integration.
  rewrite <- integration_linear_mult_l.
  auto.
Qed.

Definition score_meas {X} (w : X -> R+) (μ : Meas X) : Meas X :=
  μ >>= (fun x A => w x * indicator A x).

Lemma bind_of_score {A B} w μ (f : A -> Meas B) :
  score_meas w μ >>= f = μ >>= (fun a ev => (w a) * f a ev).
Proof.
  unfold score_meas.
  rewrite meas_bind_assoc.
  integrand_extensionality x.
  rewrite integration_linear_in_meas.
  fold (dirac x).
  rewrite meas_id_left.
  reflexivity.
Qed.


Lemma bind_meas_option {A B} μ (f : A -> Meas B) :
  meas_option μ >>= f =
  μ >>= (fun x ev => option0 (flip f ev <$> x)).
Proof.
  intros.
  extensionality ev.
  setoid_rewrite riemann_def_of_lebesgue_integration.
  integrand_extensionality t.
  unfold meas_option.
  f_equal.
  extensionality x.
  destruct x; cbn; auto.
  destruct ennr_gt_dec; auto.
  contradict e.
  destruct t; cbn; auto.
  apply RIneq.Rle_not_lt.
  auto.
Qed.

Lemma push_score {X Y} (f : X -> R+) (g : X -> option Y) (g_inv : Y -> option X) (μ : Meas X) :
  partial_bijection g g_inv ->
  (forall x, g x = None -> f x = 0) ->
  pushforward (score_meas f μ) g =
  score_meas (fun y => option0 (f <$> (g_inv o=<< y))) (pushforward μ g).
Proof.
  intros.
  unfold score_meas.
  rewrite 2 pushforward_as_bind.
  repeat rewrite meas_bind_assoc.
  integrand_extensionality x.
  unfold compose.
  rewrite meas_id_left.
  rewrite integration_linear_in_meas.
  fold (dirac x).
  rewrite meas_id_left.
  remember (g x).
  destruct o; cbn. {
    rewrite (proj1 (H x y)); auto.
  } {
    rewrite H0; auto.
  }
Qed.

Lemma push_score' {X Y}
      (f : X -> R+) (g : X -> Y)
      (g_inv : Y -> option X)
      (μ : Meas X) :
  let f' x := option0 (f <$> x) in
  (forall x, f x = f' (g_inv (g x))) ->
  pushforward (score_meas f μ) g =
  score_meas (fun y => f' (g_inv y)) (pushforward μ g).
Proof.
  intros.
  unfold score_meas.
  rewrite 2 pushforward_as_bind.
  repeat rewrite meas_bind_assoc.
  integrand_extensionality x.
  unfold compose.
  rewrite meas_id_left.

  rewrite integration_linear_in_meas.
  fold (dirac x).
  rewrite meas_id_left.
  f_equal.
  apply H.
Qed.

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





(* new, scary stuff *)

Definition lebesgue0 (a b : R) : R+ :=
  finite (Rmax a b - Rmin a b) (max_sub_min_is_pos _ _).

Definition Rmonotone (f : R -> R) :=
  (forall a b, a <= b -> f a <= f b)%R.

(* Axiom lebesgue_translate_invariant : *)
(*   forall r, lebesgue_measure = pushforward lebesgue_measure (Rplus r). *)

(* Axiom lebesgue_opp_invariant : lebesgue_measure = pushforward lebesgue_measure Ropp. *)

Definition is_RN_deriv_traditional {X} (ν : Meas X) (μ : Meas X) (f : X -> R+) : Prop :=
  forall A,
    ν A = integration (fun x => indicator A x * f x) μ.

(* a more bind-y way to write it *)
Definition is_RN_deriv {X} (ν : Meas X) (μ : Meas X) (f : X -> R+) : Prop :=
    ν = μ >>= (fun x A => indicator A x * f x).

Lemma RN_defs_equiv {X} (ν μ : Meas X) f :
  is_RN_deriv ν μ f <-> is_RN_deriv_traditional ν μ f.
Proof.
  unfold is_RN_deriv, is_RN_deriv_traditional, ">>=".
  split; intros. {
    rewrite H.
    auto.
  } {
    extensionality A.
    apply H.
  }
Qed.

(* Is this even true? *)
Axiom RN_deriv_is_coq_deriv_partial :
  forall (f f_inv : R -> option R) (D_f_inv : R -> option R+) (H : partially_derivable f),
    (* (forall y, f o=<< (f_inv o=<< y) o<= y) -> *)
    (* (forall x, f_inv o=<< (f o=<< x) o<= x) -> *)
    partial_bijection f f_inv ->
    (forall y, D_f_inv y = ennr_inv <$> (ennr_abs <$> (partially_derive f H o=<< (f_inv y)))) ->
    is_RN_deriv
      (meas_option (pushforward lebesgue_measure f))
      lebesgue_measure
      (option0 ∘ D_f_inv).

Lemma RN_deriv_is_coq_deriv_total :
  forall (f f_inv : R -> R) (D_f_inv : R -> R+) (H : derivable f),
    (forall y, f (f_inv y) = y) ->
    (forall x, f_inv (f x) = x) ->
    (forall y, D_f_inv y = / (ennr_abs (derive f H (f_inv y)))) ->
    is_RN_deriv
      (pushforward lebesgue_measure f)
      lebesgue_measure
      D_f_inv.
Proof.
  intros.
  pose proof RN_deriv_is_coq_deriv_partial (Some ∘ f) (Some ∘ f_inv) (Some ∘ D_f_inv).
  unfold compose in *.
  cbn in *.

  replace (meas_option (pushforward lebesgue_measure (fun x => Some (f x))))
  with (pushforward lebesgue_measure f)
    in * by reflexivity.

  unshelve eapply H3; clear H3; intros. {
    repeat intro.
    unfold compose.
    cbn.
    apply H.
  } {
    split; intros. {
      inject H3.
      rewrite H1.
      reflexivity.
    } {
      inject H3.
      rewrite H0.
      reflexivity.
    }
  } {
     rewrite H2.
     reflexivity.
  }
Qed.