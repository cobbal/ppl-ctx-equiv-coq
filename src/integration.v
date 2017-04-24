(** This file axiomatizes the needed definitions and properties of the Lebesgue
    integral. It ignores all issues of measurability, but otherwise attempts to
    only axiomatize well-known results in analysis and measure theory. *)

Require Import utils.
Require Import entropy.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.

(** * Definitions *)

(** Using [bool] instead of [Prop] for the definition of an event is a little
    unusual, but allows us to define an indicator function that produces real
    numbers (which are in the [Set] universe). It's very possible there are
    other solutions to this problem, such as using
    [excluded_middle_informative]. *)
Definition Event X := X -> bool.
Definition Meas A := (Event A -> R+).

(** [ifte] is a function version of "if then else" which allows tactics like
    f_equal can deal with it more easily. *)
Definition ifte {X} (a : bool) (b c : X) := if a then b else c.
Definition indicator {X} (b : Event X) : X -> R+ := fun x => ifte (b x) 1 0.

Definition full_event {X} : Event X := const true.

Definition bool_of_dec {X Y} : sumbool X Y -> bool :=
  fun xy => if xy then true else false.

(** * Axioms of integration *)

(** Assume that integration exists for all (non-negative) functions. *)
Axiom integration : forall {A}, (A -> R+) -> Meas A -> R+.

(** Assume the general form of linearity for integration. *)
Axiom integration_linear :
  forall {A} (μ : Meas A) (s0 s1 : R+) (f0 f1 : A -> R+),
    s0 * integration f0 μ + s1 * integration f1 μ =
    integration (fun x => s0 * f0 x + s1 * f1 x) μ.

(** In order to do any useful integration, we will need to axiomatize several
    measures involving real numbers. *)

(** Assume that [Entropy] has a probability measure on it *)
Axiom μEntropy : Meas Entropy.
Axiom μEntropy_is_a_probability_measure : μEntropy full_event = 1.

(** Assume the Lebesgue measure restricted to non-negative reals. Throw in ∞
    too, but it's just one point so it has no mass. *)
Axiom lebesgue_pos_measure : Meas R+.

(** Assume lebesgue([0, r]) = r *)
Axiom lebesgue_pos_measure_interval :
  forall (r : R+),
    lebesgue_pos_measure (fun x => bool_of_dec (ennr_gt_dec r x)) = r.

(** Assume that Lebesgue integration can be expressed as a Riemann integral of
    the "layer cake" function. (Leib and Loss, 1997).

    Despite the promise in the name to relate Lebesgue and Riemann integrals, it
    is phrased here as a relation just between Lebesgue and Lebesgue. Since the
    Lebesuge integral is defined strictly more often than and always agrees with
    the Riemann integral, this is still a valid assumption.

    This assumption turns out to be very useful for proving equalities of
    integrals between measure-isomorphic domains. It also can provide a way to
    deal with integration by non-axiomatized measures, e.g. pushfowards. *)
Axiom riemann_def_of_lebesgue_integration :
  forall {A} μ (f : A -> R+),
    integration f μ =
    integration
      (fun t => μ (fun x => bool_of_dec (ennr_gt_dec (f x) t)))
      lebesgue_pos_measure.

(** This assumption is usually presented as the first step in the definition of
    the Lebesgue integral. *)
Axiom integration_of_indicator :
  forall {A} (μ : Meas A) (f : Event A),
    integration (indicator f) μ = μ f.

(** (Lemma 5 in paper) This axiom states that entropy can be split into 2 IID
    entropies. *)
Axiom integration_πL_πR : forall (g : Entropy -> Entropy -> R+),
    integration (fun σ => g (πL σ) (πR σ)) μEntropy =
    integration (fun σL => integration (fun σR => g σL σR) μEntropy) μEntropy.

(** Define convenient, Haskelly syntax for working with markov kernels as a
    monad in the spirit of Giry (1980) and Panangaden (1999). For lack of a
    better name, let's call the SRel+ because we're removing the subprobability
    restriction from SRel. *)
Definition meas_bind {A B} (μ : Meas A) (f : A -> Meas B) : Meas B :=
  fun ev => integration (fun a => f a ev) μ.
Infix ">>=" := meas_bind (at level 20).

(** This is the associativity law for SRel+. Panangaden proved this for
    subprobabilities, but his proof makes no use of that restriction, and is
    therefore just as good of a proof in this instance. *)
Axiom meas_bind_assoc : forall {A B C} (μ : Meas A) (f : A -> Meas B) (g : B -> Meas C),
  (μ >>= f) >>= g = μ >>= (fun x => f x >>= g).

(** An actual definition of σ-finite here would be more challenging than
    rewarding, so we instead simply construct a short whitelist of measures that
    are known to be sigma finite and are safe to apply Tonelli's theorem to. *)
Inductive KnownToBeSigmaFinite : forall {A}, Meas A -> Prop :=
| ent_finite : KnownToBeSigmaFinite μEntropy
| leb_finite : KnownToBeSigmaFinite lebesgue_pos_measure.
Hint Constructors KnownToBeSigmaFinite.

(** We axiomitize Tonelli's theorem for all combinations of the two measures
    listed above. *)
Axiom tonelli_sigma_finite :
  forall {A B} (f : A -> B -> R+) (μx : Meas A) (μy : Meas B),
    KnownToBeSigmaFinite μx ->
    KnownToBeSigmaFinite μy ->
    integration (fun x => integration (fun y => f x y) μy) μx =
    integration (fun y => integration (fun x => f x y) μx) μy.

(** * Consequences of the axioms *)

(** ** Measure combinators *)

Definition empty_meas A : Meas A := fun a => 0.
Arguments empty_meas _ _ /.

Definition dirac {A} (v : A) : Meas A :=
  fun e => indicator e v.
Arguments dirac {_} _ _ /.

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

(** Two ways to reweight a [Meas A]. [unif_score_meas] reweights the entire
    measure by a constant. [score_meas] reweights dependent on each element in [A]. *)
Definition score_meas {X} (w : X -> R+) (μ : Meas X) : Meas X :=
  μ >>= (fun x A => w x * indicator A x).

Definition unif_score_meas {X} (s : R+) (μ : Meas X) : Meas X :=
  fun A => μ A * s.
Arguments unif_score_meas {_} _ _ _ /.


(** ** Lemmas about integrals *)

(** Tactic for showing [∫ f dμ = ∫ g dμ] by pointwise equality of [f] and [g]. *)
Ltac integrand_extensionality x :=
  match goal with
  | [ |- _ = _ :> R+ ] => idtac
  | [ |- _ = _ :> Meas _ ] => let A := fresh "A" in extensionality A
  | [ |- _ = _ :> _ -> R+ ] => let A := fresh "A" in extensionality A
  end;
  refine (f_equal2 integration _ eq_refl);
  extensionality x.

(** Derive some more immediately useful forms of linearity. *)
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

Lemma integration_linear_in_meas {A B} (μ : Meas A) (s : R+) (f : A -> Meas B) :
  (fun ev => s * μ ev) >>= f =
  (fun ev => s * (μ >>= f) ev).
Proof.
  extensionality ev.
  setoid_rewrite riemann_def_of_lebesgue_integration.
  rewrite <- integration_linear_mult_l.
  auto.
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

(** Some lemmas about integrating by the new measures *)
Lemma integration_of_pushforward {A B} (g : A -> B) f μ :
  integration (f ∘ g) μ = integration f (pushforward μ g).
Proof.
  intros.
  setoid_rewrite riemann_def_of_lebesgue_integration.
  unfold pushforward, preimage, compose.
  trivial.
Qed.

Lemma bind_empty {A B} f :
  empty_meas A >>= f = empty_meas B.
Proof.
  extensionality ev.
  setoid_rewrite riemann_def_of_lebesgue_integration.
  unfold empty_meas.
  apply integration_of_0.
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


(** The remaining two monad laws for SRel+ *)

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

Definition meas_join {A} (μ : Meas (Meas A)) : Meas A := μ >>= id.
Definition kernel A B := A -> Meas B.

(** * Measures that may be safely interchanged *)

(** Tonelli's theorem will be too restricted to be of immediate use in dealing
    with some of our measures. We will need to prove a wider class of measures
    than just sigma-finite ones can be involved in an integral interchange. *)
Class interchangable {A B} (μa : Meas A) (μb : Meas B) : Prop :=
  interchange : (forall {C} (f : A -> B -> Meas C),
                    μa >>= (fun a => μb >>= (fun b => f a b)) =
                    μb >>= (fun b => μa >>= (fun a => f a b))).

(** [interchangable] is a symmetric relation. Unfortunately we can't use the
    [Symmetry] typeclass because it's a relation between different types. *)
Definition interchangable_sym {A B} (μa : Meas A) (μb : Meas B) :
  interchangable μa μb ->
  interchangable μb μa.
Proof.
  repeat intro.
  symmetry.
  apply H.
Qed.

Instance sigma_finite_is_interchangable {A B} (μa : Meas A) (μb : Meas B) :
  KnownToBeSigmaFinite μa ->
  KnownToBeSigmaFinite μb ->
  interchangable μa μb.
Proof.
  repeat intro.
  extensionality ev.
  apply tonelli_sigma_finite; auto.
Qed.

Instance score_meas_interchangable {X} (μ : Meas X) (w : X -> R+) :
  forall {Y} (μy : Meas Y),
    interchangable μ μy ->
    interchangable (score_meas w μ) μy.
Proof.
  repeat intro.

  setoid_rewrite meas_bind_assoc.
  rewrite <- H; auto.

  extensionality A.
  integrand_extensionality x.

  rewrite integration_linear_in_meas.
  setoid_rewrite integration_linear_in_meas.
  setoid_rewrite <- integration_linear_mult_l.
  f_equal.
  fold (dirac x).
  rewrite meas_id_left.
  integrand_extensionality y.
  rewrite meas_id_left.
  reflexivity.
Qed.

Instance pushforward_interchangable {X Y} (μ : Meas X) (f : X -> Y) :
  forall {Z} (μz : Meas Z),
    interchangable μ μz ->
    interchangable (pushforward μ f) μz.
Proof.
  repeat intro.

  unfold ">>=".

  setoid_rewrite <- (integration_of_pushforward f).

  extensionality ev.
  change ((μ >>= (fun x => μz >>= (fun z => (f0 ∘ f) x z))) ev =
          (μz >>= (fun z => μ >>= (fun x => (f0 ∘ f) x z))) ev).
  rewrite H; auto.
Qed.

Instance meas_option_interchangable {X} (μ : Meas (option X)) :
  forall {Y} (μy : Meas Y),
    interchangable μ μy ->
    interchangable (meas_option μ) μy.
Proof.
  repeat intro.

  setoid_rewrite bind_meas_option.
  rewrite <- H; auto.

  extensionality ev.
  integrand_extensionality o.

  destruct o; cbn; auto.
  setoid_rewrite integration_of_0.
  trivial.
Qed.

Lemma bind_interchangable {X Z} (μ : Meas X) (f : X -> Meas Z) :
  forall {Y} (μy : Meas Y),
    interchangable μ μy ->
    (forall x, interchangable (f x) μy) ->
    interchangable (μ >>= f) μy.
Proof.
  repeat intro.
  setoid_rewrite meas_bind_assoc.
  rewrite <- H.

  f_equal.
  extensionality x.

  apply H0.
Qed.

(** ** Other lemmas *)

(** Use the fact that [μEntropy] is a probability measure to lift constant
    functions out of integrals. *)
Lemma integration_const_entropy :
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

(** Repharse [integration_πL_πR] in terms of [>>=] *)
Lemma bind_πL_πR {B} (g : Entropy -> Entropy -> Meas B) :
  μEntropy >>= (fun σ => g (πL σ) (πR σ)) =
  μEntropy >>= (fun σL => μEntropy >>= (fun σR => g σL σR)).
Proof.
  extensionality ev.
  unfold ">>=".
  rewrite <- integration_πL_πR.
  auto.
Qed.

(** Apply [bind_πL_πR] thrice in a convenient-to-use manner *)
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

(** Even more convenient ways to apply [bind_πL_πR]! These are very similar to
    what the evaluation relation will look like, and will be easily be applied
    there. *)
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
  setoid_rewrite integration_const_entropy; auto.
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
  setoid_rewrite integration_const_entropy; auto.
Qed.

(** Lemma 5 in paper *)
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

  specialize (f_is_M_measurable (fun fx => bool_of_dec (ennr_gt_dec fx t))).
  unfold preimage in f_is_M_measurable.
  exact f_is_M_measurable.
Qed.

Lemma coarsening' :
  forall {X0 X1}
         (M : Event X0 -> Event X1 -> Prop)
         (μ0 : Meas X0)
         (μ1 : Meas X1)
         (f0 : X0 -> R+)
         (f1 : X1 -> R+)
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

  specialize (f_is_M_measurable (fun fx => bool_of_dec (ennr_gt_dec fx t))).
  unfold preimage in f_is_M_measurable.
  exact f_is_M_measurable.
Qed.