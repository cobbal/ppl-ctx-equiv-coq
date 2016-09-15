Require Import Basics.
Require Import Equality.
Require Import Coquelicot.Coquelicot.
Require Import Reals.
Require Import Fourier.
Require Import List.
Require Import Ensembles.
Require Import nnr.
Require Import utils.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import MeasureTheory.SetsExtra.
Require Import Classical.
Require Import RelationClasses.

(* Require Import MeasureTheory.SigmaAlgebra. *)
(* Require Import MeasureTheory.RBorel. *)
(* Require Import MeasureTheory.Topology. *)
(* Require Import MeasureTheory.Base. *)
Require Import propifications.
(* Require Import Interval.Interval_tactic. *)


Local Open Scope R.

Definition nnrbar := {r : Rbar | 0 <= r}.
Definition _rbar : nnrbar -> Rbar := @proj1_sig _ _.

Definition CountableUnion {X} (f : nat -> Ensemble X) : Ensemble X :=
  fun x => exists n, x ∈ f n.

Definition CountableIntersection {X} (f : nat -> Ensemble X) : Ensemble X :=
  fun x => forall n, x ∈ f n.

Instance Rle_Reflexive : Reflexive Rle := Rle_refl.
Instance Rle_Transitive : Transitive Rle := Rle_trans.

Record SigmaAlgebra {X} :=
  { Σ_sets :> Ensemble (Ensemble X);
    Σ_contains_full : Full_set ∈ Σ_sets;
    Σ_closed_complement {s} : s ∈ Σ_sets -> ¬ s ∈ Σ_sets;
    Σ_closed_countable_union (f : nat -> Ensemble X) :
      (forall n, f n ∈ Σ_sets) ->
      CountableUnion f ∈ Σ_sets;
    Σ_closed_extensional : forall A B,
        A ≈ B ->
        A ∈ Σ_sets ->
        B ∈ Σ_sets;

  }.
Arguments SigmaAlgebra _ : clear implicits.

Lemma Σ_contains_empty {X} (Σ : SigmaAlgebra X)
  : Empty_set ∈ Σ.
Proof.
  apply (Σ_closed_extensional _ (¬ Full_set)). {
    split. {
      intros ? ?.
      unfold Complement, In in *.
      contradict H.
      constructor.
    } {
      intros ? ?.
      inversion H.
    }
  } {
    apply Σ_closed_complement.
    apply Σ_contains_full.
  }
Qed.

Lemma Σ_closed_countable_intersection {X} (Σ : SigmaAlgebra X) :
  forall (f : nat -> Ensemble X),
    (forall n, f n ∈ Σ) ->
    CountableIntersection f ∈ Σ.
Proof.
  intros.
  apply (Σ_closed_extensional _ (¬ (CountableUnion (fun x => ¬ f x)))). {
    split. {
      intros ? ? ?.
      unfold compose, CountableUnion, Complement, In in *.
      elim (classic (f n x)); auto.
      intros.
      contradict H0.
      exists n; auto.
    } {
      intros ? ? ?.
      destruct H1 as [n ?].
      unfold Complement, In, compose in *.
      apply H1.
      apply H0.
    }
  } {
    apply Σ_closed_complement.
    apply Σ_closed_countable_union.
    intro.
    apply Σ_closed_complement.
    apply H.
  }
Qed.

Definition bin_union {X} (A B : Ensemble X) : Ensemble X :=
  fun x => x ∈ A \/ x ∈ B.
Definition bin_int {X} (A B : Ensemble X) : Ensemble X :=
  fun x => x ∈ A /\ x ∈ B.

Notation "A ∪ B" := (bin_union A B) (at level 40).
Notation "A ∩ B" := (bin_int A B) (at level 40).

Lemma Σ_closed_bin_union {X} (Σ : SigmaAlgebra X) :
  forall (A B : Ensemble X),
    A ∈ Σ -> B ∈ Σ ->
    A ∪ B ∈ Σ.
Proof.
  intros.
  apply (Σ_closed_extensional
           _ (CountableUnion
                (fun n =>
                   match n with
                   | 0%nat => A
                   | 1%nat => B
                   | _ => Empty_set
                   end))
           _). {
    split. {
      intros ? ?.
      unfold CountableUnion, In in H1.
      destruct H1 as [n ?].
      destruct n; [left; auto |].
      destruct n; [right; auto |].
      inversion H1.
    } {
      intros ? ?.
      destruct H1; [exists 0%nat | exists 1%nat]; auto.
    }
  } {
    apply Σ_closed_countable_union.
    intros.
    destruct n; auto.
    destruct n; auto.
    apply Σ_contains_empty.
  }
Qed.

Lemma Σ_closed_bin_intersection {X} (Σ : SigmaAlgebra X) :
  forall (A B : Ensemble X),
    A ∈ Σ -> B ∈ Σ ->
    A ∩ B ∈ Σ.
Proof.
  intros.
  apply (Σ_closed_extensional
           _ (CountableIntersection
                (fun n =>
                   match n with
                   | 0%nat => A
                   | 1%nat => B
                   | _ => Full_set
                   end))
           _). {
    split. {
      intros ? ?.
      unfold CountableIntersection, In in H1.
      split; [apply (H1 0%nat) | apply (H1 1%nat)].
    } {
      intros ? ? ?.
      destruct H1.
      destruct n; auto.
      destruct n; auto.
      constructor.
    }
  } {
    apply Σ_closed_countable_intersection.
    intros.
    destruct n; auto.
    destruct n; auto.
    apply Σ_contains_full.
  }
Qed.

Inductive generate_Σ_sets {X} (F : Ensemble (Ensemble X)) : Ensemble (Ensemble X) :=
| gen_Σ_base f : f ∈ F -> f ∈ generate_Σ_sets F
| gen_Σ_full : Full_set ∈ generate_Σ_sets F
| gen_Σ_complement f : f ∈ generate_Σ_sets F -> ¬ f ∈ generate_Σ_sets F
| gen_Σ_union f : (forall n : nat , f n ∈ generate_Σ_sets F) ->
    CountableUnion f  ∈ generate_Σ_sets F
| gen_Σ_exestential : forall A B,
    A ≈ B ->
    A ∈ generate_Σ_sets F ->
    B ∈ generate_Σ_sets F
.

Definition generate_Σ {X} (F : Ensemble (Ensemble X)) : SigmaAlgebra X :=
  Build_SigmaAlgebra
    X
    (generate_Σ_sets F)
    (gen_Σ_full F)
    (gen_Σ_complement F)
    (gen_Σ_union F)
    (gen_Σ_exestential F).

Definition unitR := {r : R | 0 <= r <= 1}.

Record subunit_ivl :=
  mk_subunit_ivl
    { sui_lo : {r : R | 0 <= r <= 1};
      sui_hi : {r : R | 0 <= r <= 1};
      sui_lo_hi : proj1_sig sui_lo <= proj1_sig sui_hi;
    }.
Definition in_ivl (i : subunit_ivl) (r : R) := proj1_sig (sui_lo i) < r < proj1_sig (sui_hi i).

Definition unitR_open_set (i : subunit_ivl) : Ensemble unitR :=
  fun x => in_ivl i (proj1_sig x).

Definition Σ_unitR := generate_Σ (fun s => exists l, unitR_open_set l ≈ s).

Lemma unitROpenIvl (i : subunit_ivl) : unitR_open_set i ∈ Σ_unitR.
Proof.
  constructor.
  eexists.
  reflexivity.
Qed.

Definition countably_disjoint {X} (f : nat -> Ensemble X) :=
  forall m n : nat, m <> n -> f m ∩ f n ≈ Empty_set.

Record FMeas {X : Type} {Σ : SigmaAlgebra X} :=
  { meas_rel {E : Ensemble X} :> E ∈ Σ -> one R+ _;
    meas_null : forall (s : Empty_set ∈ Σ), meas_rel s nnr_0;
    meas_extensional {E0 E1 : Ensemble X}
                     (s0 : E0 ∈ Σ) (s1 : E1 ∈ Σ) (r : R+) :
      E0 = E1 -> meas_rel s0 r -> meas_rel s1 r;
    meas_countable_additive :
      forall
        (Es : nat -> Ensemble X)
        (ss : forall n, Es n ∈ Σ)
        (rs : nat -> R+)
        (r : R+),
        (forall n, meas_rel (ss n) (rs n)) ->
        countably_disjoint Es ->
        infinite_sum (_r ∘ rs) (_r r) ->
        meas_rel (Σ_closed_countable_union Σ Es ss) r
  }.
Arguments FMeas {_} _.

Program Fixpoint μ_unitR_base_fn (i : subunit_ivl) : R+ :=
  mknnr (sui_hi i - sui_lo i) _.
Next Obligation.
  destruct i.
  simpl.
  fourier.
Qed.

Inductive μ_unitR_rel : forall {E}, E ∈ Σ_unitR -> R+ -> Prop :=
| μ_unitR_fn_base i :
    μ_unitR_rel (unitROpenIvl i) (μ_unitR_base_fn i)
| μ_unitR_fn_sum
    (f : nat -> Ensemble unitR)
    (Hf : forall n, f n ∈ Σ_unitR)
    (rs : nat -> R+)
    (r : R+)
    (Hrs : forall n, μ_unitR_rel (Hf n) (rs n)) :
    countably_disjoint f ->
    infinite_sum (_r ∘ rs) (_r r) ->
    μ_unitR_rel (Σ_closed_countable_union _ f Hf) r
.

Instance ss_equiv {U} : Equivalence (@Same_set U).
Proof.
  constructor; intros ?; intros; auto with Sets.
Qed.

Lemma ivl_common_dec (i0 i1 : subunit_ivl) :
  {exists e : {r | 0 <= r <= 1}, in_ivl i0 (proj1_sig e) /\ in_ivl i1 (proj1_sig e)} +
  {proj1_sig (sui_hi i0) < proj1_sig (sui_lo i1)} +
  {proj1_sig (sui_hi i1) < proj1_sig (sui_lo i0)}.
Proof.
  destruct_ivl i0.
  destruct_ivl i1.
  simpl.
  destruct (Rlt_dec i0_hi i1_lo). {
    left; right; assumption.
  }
  destruct (Rlt_dec i1_hi i0_lo). {
    right; assumption.
  }
  left; left.
  apply Rnot_lt_le in n.
  apply Rnot_lt_le in n0.
  unfold in_ivl.
  simpl.
  pose (x := Rmax i0_lo i1_lo).
  assert (0 <= x <= 1). {
    subst x.
    unfold Rmax.
    break_conj.
    destruct Rle_dec; split; auto.
  }
  exists (exist _ x H).
  simpl.
  subst x.
  unfold Rmax.
  break_conj.
  destruct Rle_dec; repeat split; auto; try reflexivity.
  apply Rnot_le_lt in n1.
  fourier.
Qed.

Program Fixpoint a_point_in_a_cylinder (c : cylinder) : Entropy :=
    match c with
    | nil => constEntropy 0 _
    | (i :: c') =>
      fun n =>
        match n with
        | O => sui_lo i
        | S n'  => a_point_in_a_cylinder c' n'
        end
    end.
Next Obligation.
  split; fourier.
Qed.

Lemma a_point_in_a_cylinder_is_in_the_cylinder (c : cylinder) :
  a_point_in_a_cylinder c ∈ EntropyOpenCylinder_set c.
Proof.
  induction c; try solve [constructor].
  split. {
    unfold in_ivl.
    destruct a; simpl; split; try fourier.
  } {
    unfold compose.
    simpl.
    exact IHc.
  }
Qed.

Definition EntropyCons (r : {r | 0 <= r <= 1}) (σ : Entropy) : Entropy :=
  fun n =>
    match n with
    | O => r
    | S n' => σ n'
    end.

Lemma EntropyConsS r σ : (EntropyCons r σ) ∘ S = σ.
Proof.
  extensionality n.
  unfold compose, EntropyCons.
  reflexivity.
Qed.

Program Definition μEntropy_fn {E} (HE : E ∈ Σ_Entropy) : one R+ _ :=
  mk_one (μEntropy_rel HE) _ _.
Next Obligation.




Fail.





































































Definition Entropy := nat -> {r : R | 0 <= r <= 1}.
Record subunit_ivl :=
  mk_subunit_ivl
    { sui_lo : {r : R | 0 <= r <= 1};
      sui_hi : {r : R | 0 <= r <= 1};
      sui_lo_hi : proj1_sig sui_lo <= proj1_sig sui_hi;
    }.
Definition cylinder := list subunit_ivl.
Ltac destruct_ivl i :=
  let lo := fresh i "_lo" in
  let hi := fresh i "_hi" in
  let Hlo := fresh "H_" lo in
  let Hhi := fresh "H_" hi in
  let Hlohi := fresh "H" i "lohi" in
  destruct i as [[lo Hlo] [hi Hhi] Hlohi]; unfold proj1_sig in Hlohi.
Ltac break_conj :=
  repeat match goal with
         | [ H : _ /\ _ |- _ ] =>
           let Hl := fresh H "l" in
           let Hr := fresh H "r" in
           destruct H as [Hl Hr]
         end.

Ltac order_hyps l :=
  let rec order_hyps' prev l :=
      match l with
      | tt => idtac
      | (?H, ?l') =>
        move H before prev;
        order_hyps' H l'
      end in
  match l with
  | (?H0, ?Hrst) => move H0 at top; order_hyps' H0 Hrst
  end.

Fixpoint EntropyOpenCylinder_set (c : cylinder) : Ensemble Entropy :=
  match c with
  | nil => Full_set
  | sui :: l' =>
    fun σ =>
      in_ivl sui (proj1_sig (σ O)) /\
      EntropyOpenCylinder_set l' (σ ∘ S)
  end.

Definition Σ_Entropy := generate_Σ (fun s => exists l, EntropyOpenCylinder_set l ≈ s).

Lemma EntropyOpenCylinder (c : cylinder) : EntropyOpenCylinder_set c ∈ Σ_Entropy.
Proof.
  constructor.
  eexists.
  reflexivity.
Qed.


(* Fixpoint EntropyOpenCylinder_Intersection *)
(*          (l0 l1 : list (R ⨉ R)) : list (R ⨉ R) := *)
(*   match l0, l1 with *)
(*   | _, nil => l0 *)
(*   | nil, _ => l1 *)
(*   | (lo0, hi0) :: l0', (lo1, hi1) :: l1' => *)
(*     (Rmax lo0 lo1, Rmin hi0 hi1) :: EntropyOpenCylinder_Intersection l0' l1' *)
(*   end. *)

(* Hint Unfold In. *)

(* Lemma EntropyOpenCylinder_Intersection_is_intersection ivl0 ivl1 : *)
(*   EntropyOpenCylinder *)
(*     (EntropyOpenCylinder_Intersection ivl0 ivl1) ≈ *)
(*     EntropyOpenCylinder ivl0 ∩ EntropyOpenCylinder ivl1. *)
(* Proof. *)
(*   revert ivl1. *)
(*   induction ivl0; induction ivl1; simpl; intros. { *)
(*     split; intros ? ?. { *)
(*       apply BinaryIntersection_both; auto. *)
(*     } { *)
(*       exact (BinaryIntersection_l H). *)
(*     } *)
(*   } { *)
(*     split; intros ? ?. { *)
(*       apply BinaryIntersection_both; auto. *)
(*       constructor. *)
(*     } { *)
(*       exact (BinaryIntersection_r H). *)
(*     } *)
(*   } { *)
(*     destruct a. *)
(*     split; intros ? ?. { *)
(*       apply BinaryIntersection_both; auto. *)
(*       constructor. *)
(*     } { *)
(*       exact (BinaryIntersection_l H). *)
(*     } *)
(*   } { *)
(*     destruct a, a0. *)
(*     split; intros ? ?. { *)
(*       unfold In in *. *)
(*       destruct H. *)
(*       apply BinaryIntersection_both. { *)
(*         split. { *)
(*           destruct H. *)
(*           split. { *)
(*             eapply Rle_trans; eauto. *)
(*             apply Rmax_l. *)
(*           } { *)
(*             eapply Rle_trans; eauto. *)
(*             apply Rmin_l. *)
(*           } *)
(*         } { *)
(*           specialize (IHivl0 ivl1). *)
(*           destruct IHivl0. *)
(*           exact (BinaryIntersection_l (H1 _ H0)). *)
(*         } *)
(*       } { *)
(*         split. { *)
(*           destruct H. *)
(*           split. { *)
(*             eapply Rle_trans; eauto. *)
(*             apply Rmax_r. *)
(*           } { *)
(*             eapply Rle_trans; eauto. *)
(*             apply Rmin_r. *)
(*           } *)
(*         } { *)
(*           specialize (IHivl0 ivl1). *)
(*           destruct IHivl0. *)
(*           exact (BinaryIntersection_r (H1 _ H0)). *)
(*         } *)
(*       } *)
(*     } { *)
(*       destruct (BinaryIntersection_l H) as [[Hlo0 Hhi0] IH0]. *)
(*       destruct (BinaryIntersection_r H) as [[Hlo1 Hhi1] IH1]. *)
(*       clear H. *)
(*       simpl. *)
(*       split. { *)
(*         split; [apply Rmax_lub | apply Rmin_glb]; auto. *)
(*       } { *)
(*         specialize (IHivl0 ivl1). *)
(*         apply IHivl0. *)
(*         apply BinaryIntersection_both; auto. *)
(*       } *)
(*     } *)
(*   } *)
(* Qed. *)


(* Inductive EntropyOpenCylinders : Ensemble (Ensemble Entropy) := *)
(* | EntropyOpenCylinders_intro : forall (I : Ensemble Entropy) ivls, *)
(*     I ≈ EntropyOpenCylinder ivls -> I ∈ EntropyOpenCylinders. *)

(* Lemma EntropyOpenCylinders_Full_set : Full_set ∈ EntropyOpenCylinders. *)
(* Proof. *)
(*   apply (EntropyOpenCylinders_intro _ nil). *)
(*   split. { *)
(*     intros ? ?. *)
(*     simpl. *)
(*     auto. *)
(*   } { *)
(*     simpl. *)
(*     constructor. *)
(*   } *)
(* Qed. *)

(* Lemma EntropyOpenCylinders_cover : Full_set ⊆ Union EntropyOpenCylinders. *)
(* Proof. *)
(*   eapply Union_Included_compat. *)
(*   reflexivity. *)
(*   apply EntropyOpenCylinders_Full_set. *)
(* Qed. *)

(* Lemma EntropyOpenCylinders_dense : forall B1 B2, *)
(*     B1 ∈ EntropyOpenCylinders -> *)
(*     B2 ∈ EntropyOpenCylinders -> *)
(*     forall x, *)
(*       x ∈ B1 ∩ B2 -> *)
(*       exists B3 : Ensemble Entropy, x ∈ B3 /\ B3 ∈ EntropyOpenCylinders /\ B3 ⊆ B1 ∩ B2. *)
(* Proof. *)
(*   intros B1 B2 HB1 HB2 x Hx_B. *)
(*   destruct HB1 as [B1 ivl1 HB1]. *)
(*   destruct HB2 as [B2 ivl2 HB2]. *)

(*   exists (EntropyOpenCylinder (EntropyOpenCylinder_Intersection ivl1 ivl2)). *)
(*   repeat constructor. { *)
(*     apply EntropyOpenCylinder_Intersection_is_intersection. *)
(*     rewrite <- HB1, <- HB2. *)
(*     auto. *)
(*   } { *)
(*     econstructor. *)
(*     reflexivity. *)
(*   } { *)
(*     rewrite EntropyOpenCylinder_Intersection_is_intersection in H. *)
(*     rewrite <- HB1, <- HB2 in H. *)
(*     destruct H. *)
(*     auto. *)
(*   } *)
(* Qed. *)

(* Lemma EntropyOpenCylinders_extensional : forall A B, *)
(*     A ≈ B -> *)
(*     A ∈ EntropyOpenCylinders -> *)
(*     B ∈ EntropyOpenCylinders. *)
(* Proof. *)
(*   intros A B HAB HA. *)
(*   destruct HA as [I ivls HI]. *)
(*   econstructor. *)
(*   rewrite <- HAB, HI. *)
(*   reflexivity. *)
(* Qed. *)

(* Definition Entropy_Base : Base Entropy := *)
(*   mkBase EntropyOpenCylinders *)
(*          EntropyOpenCylinders_cover *)
(*          EntropyOpenCylinders_dense *)
(*          EntropyOpenCylinders_extensional. *)

(* Definition Entropy_Topology : Topology Entropy := *)
(*   make_Topology_from_Base Entropy_Base. *)

(* Definition Σ_Entropy : SigmaAlgebra Entropy := *)
(*   make_SigmaAlgebra_from_Topology Entropy_Topology. *)

Definition countably_disjoint {X} (f : nat -> Ensemble X) :=
  forall m n : nat, m <> n -> f m ∩ f n ≈ Empty_set.

Record FMeas {X : Type} {Σ : SigmaAlgebra X} :=
  { meas_rel {E : Ensemble X} :> E ∈ Σ -> one R+ _;
    meas_null : forall (s : Empty_set ∈ Σ), meas_rel s nnr_0;
    meas_extensional {E0 E1 : Ensemble X}
                     (s0 : E0 ∈ Σ) (s1 : E1 ∈ Σ) (r : R+) :
      E0 = E1 -> meas_rel s0 r -> meas_rel s1 r;
    meas_countable_additive :
      forall
        (Es : nat -> Ensemble X)
        (ss : forall n, Es n ∈ Σ)
        (rs : nat -> R+)
        (r : R+),
        (forall n, meas_rel (ss n) (rs n)) ->
        countably_disjoint Es ->
        infinite_sum (_r ∘ rs) (_r r) ->
        meas_rel (Σ_closed_countable_union Σ Es ss) r
  }.
Arguments FMeas {_} _.

Program Fixpoint μEntropy_base_fn (c : cylinder) : R+ :=
  match c with
  | nil => nnr_1
  | sui :: l' =>
    mknnr (sui_hi sui - sui_lo sui) _ [*] μEntropy_base_fn l'
  end.
Next Obligation.
  destruct sui.
  simpl.
  fourier.
Qed.

Inductive μEntropy_rel : forall {E}, E ∈ Σ_Entropy -> R+ -> Prop :=
| μEntropy_fn_base c :
    μEntropy_rel (EntropyOpenCylinder c) (μEntropy_base_fn c)
| μEntropy_fn_sum
    (f : nat -> Ensemble Entropy)
    (Hf : forall n, f n ∈ Σ_Entropy)
    (rs : nat -> R+)
    (r : R+)
    (Hrs : forall n, μEntropy_rel (Hf n) (rs n)) :
    countably_disjoint f ->
    infinite_sum (_r ∘ rs) (_r r) ->
    μEntropy_rel (Σ_closed_countable_union _ f Hf) r
.

Instance ss_equiv {U} : Equivalence (@Same_set U).
Proof.
  constructor; intros ?; intros; auto with Sets.
Qed.

Definition constEntropy (r : R) (p : 0 <= r <= 1) : Entropy := fun n => exist _ r p.

Lemma μEntropy_rel_all (c : cylinder) :
  (forall σ, EntropyOpenCylinder_set c σ) ->
  μEntropy_base_fn c = nnr_1.
Proof.
  intros.
  induction c; auto.
  assert (forall σ, EntropyOpenCylinder_set c σ). {
    intros.
    specialize (H (σ ∘ pred)).
    destruct H as [_ ?].
    apply H.
  }
  specialize (IHc H0).
  clear H0.
  destruct_ivl a.
  nnr.
  simpl in *.

  assert (a_lo = 0). {
    assert (0 <= 0 <= 1) by (split; fourier).
    specialize (H (constEntropy 0 H0)).
    unfold in_ivl in H.
    simpl in H.
    destruct H as [[? ?] ?], H_a_lo.
    apply Rle_antisym; auto.
  }
  assert (a_hi = 1). {
    assert (0 <= 1 <= 1) by (split; fourier).
    specialize (H (constEntropy _ H1)).
    simpl in H.
    destruct H as [[? ?] ?], H_a_hi.
    apply Rle_antisym; auto.
  }
  subst.

  rewrite IHc.
  simpl.
  ring.
Qed.

Lemma ivl_common_dec (i0 i1 : subunit_ivl) :
  {exists e : {r | 0 <= r <= 1}, in_ivl i0 (proj1_sig e) /\ in_ivl i1 (proj1_sig e)} +
  {proj1_sig (sui_hi i0) < proj1_sig (sui_lo i1)} +
  {proj1_sig (sui_hi i1) < proj1_sig (sui_lo i0)}.
Proof.
  destruct_ivl i0.
  destruct_ivl i1.
  simpl.
  destruct (Rlt_dec i0_hi i1_lo). {
    left; right; assumption.
  }
  destruct (Rlt_dec i1_hi i0_lo). {
    right; assumption.
  }
  left; left.
  apply Rnot_lt_le in n.
  apply Rnot_lt_le in n0.
  unfold in_ivl.
  simpl.
  pose (x := Rmax i0_lo i1_lo).
  assert (0 <= x <= 1). {
    subst x.
    unfold Rmax.
    break_conj.
    destruct Rle_dec; split; auto.
  }
  exists (exist _ x H).
  simpl.
  subst x.
  unfold Rmax.
  break_conj.
  destruct Rle_dec; repeat split; auto; try reflexivity.
  apply Rnot_le_lt in n1.
  fourier.
Qed.

Program Fixpoint a_point_in_a_cylinder (c : cylinder) : Entropy :=
    match c with
    | nil => constEntropy 0 _
    | (i :: c') =>
      fun n =>
        match n with
        | O => sui_lo i
        | S n'  => a_point_in_a_cylinder c' n'
        end
    end.
Next Obligation.
  split; fourier.
Qed.

Lemma a_point_in_a_cylinder_is_in_the_cylinder (c : cylinder) :
  a_point_in_a_cylinder c ∈ EntropyOpenCylinder_set c.
Proof.
  induction c; try solve [constructor].
  split. {
    unfold in_ivl.
    destruct a; simpl; split; try fourier.
  } {
    unfold compose.
    simpl.
    exact IHc.
  }
Qed.

Definition EntropyCons (r : {r | 0 <= r <= 1}) (σ : Entropy) : Entropy :=
  fun n =>
    match n with
    | O => r
    | S n' => σ n'
    end.

Lemma EntropyConsS r σ : (EntropyCons r σ) ∘ S = σ.
Proof.
  extensionality n.
  unfold compose, EntropyCons.
  reflexivity.
Qed.

Program Definition μEntropy_fn {E} (HE : E ∈ Σ_Entropy) : one R+ _ :=
  mk_one (μEntropy_rel HE) _ _.
Next Obligation.
  rename b0 into r0, b1 into r1.

  revert H0.
  induction H. {
    intros.
    dependent destruction H0. {
      assert (forall σ, σ ∈ EntropyOpenCylinder_set c0 <-> σ ∈ EntropyOpenCylinder_set c). {
        split; rewrite x0; auto.
      }
      clear x x0.

      rename c into c0, c0 into c1.

      revert c1 H.

      induction c0, c1; intros; auto. {
        rewrite (μEntropy_rel_all (s :: c1)); auto.
        intros.
        apply H.
        constructor.
      } {
        rewrite (μEntropy_rel_all (a :: c0)); auto.
        intros.
        apply H.
        constructor.
      } {
        pose proof (a_point_in_a_cylinder_is_in_the_cylinder (a :: c0)) as p0.
        pose proof (a_point_in_a_cylinder_is_in_the_cylinder (s :: c1)) as p1.
        pose proof (proj1 (H _) p1).
        pose proof (proj2 (H _) p0).
        clear p0 p1.

        unfold In in *.
        destruct (ivl_common_dec a s) as [[[? ?] | ? ] | ?]. {
          destruct H2.
          nnr.
          simpl.
          f_equal. {
            destruct H0 as [? _], H1 as [? _].
            simpl in *.

            assert (0 <= proj1_sig (sui_hi a) <= 1). {
              destruct_ivl a.
              break_conj.
              simpl.
              split; auto.
            }
            assert (0 <= proj1_sig (sui_hi s) <= 1). {
              destruct_ivl s.
              break_conj.
              simpl.
              split; auto.
            }
            pose proof (proj2 (H (EntropyCons (exist _ _ H4) (a_point_in_a_cylinder c0)))).
            pose proof (proj1 (H (EntropyCons (exist _ _ H5) (a_point_in_a_cylinder c1)))).

            unfold EntropyCons, compose, in_ivl in H6, H7.
            simpl in *.
            destruct H6. {
              split. {
                destruct_ivl a; simpl in *.
                break_conj.
                split; auto.
                reflexivity.
              } {
                apply a_point_in_a_cylinder_is_in_the_cylinder.
              }
            }
            destruct H7. {
              split. {
                destruct_ivl s; simpl in *.
                break_conj.
                split; auto.
                reflexivity.
              } {
                apply a_point_in_a_cylinder_is_in_the_cylinder.
              }
            }

            clear H.
            destruct_ivl a.
            destruct_ivl s.
            unfold in_ivl in *.
            simpl in *.

            break_conj.
            f_equal; apply Rle_antisym; auto.
          } {
            clear H0 H1.
            f_equal.
            apply IHc0.

            intros.
            specialize (H (fun n => match n with | O => x | S n' => σ n' end)).
            destruct x as [? ?].
            simpl in *.
            unfold compose in *.
            (* destruct H0, H1. *)
            split; intro; apply H; split; auto.
          }
        } {
          contradict r.
          destruct H0 as [[_ ?] _].
          simpl in H0.
          exact (Rle_not_gt _ _ H0).
        } {
          contradict r.
          destruct H1 as [[_ ?] _].
          simpl in H1.
          exact (Rle_not_gt _ _ H1).
        }
      }
    } {
      admit.
    }
  } {
    intros.
    dependent induction H2. {
      admit.
    } {
      (* rearranging time *)
      clear H3 H x.
      rename r into r0, r0 into r1.
      rename f into f0, f0 into f1.
      rename Hf into Hf0, Hf0 into Hf1.
      rename rs into rs0, rs0 into rs1.
      rename Hrs into Hrs0, Hrs0 into Hrs1.
      rename H0 into disjoint0, H4 into disjoint1.
      rename H1 into sum0, H2 into sum1.
      rename x0 into H.
      order_hyps [f0, f1,
                  Hf0, Hf1,
                  disjoint0, disjoint1,
                  rs0, rs1,
                  Hrs0, Hrs1,
                  r0, r1,
                  sum0, sum1,
                  H].

    }
  }
Qed.



(* Proof. *)
(*   intros. *)
(*   refine (forall (I : Ensemble Entropy) (ivls : list (R ⨉ R)), _ : Prop). *)
(*   exact (μEntropy_base_fn ivls = H0) *)
(* Defined. *)

Lemma μEntropy : FMeas Σ_Entropy.
Proof.
  econstructor. {
    intros.

  }
Qed.

Axiom μEntropy : FMeas Entropy.

Inductive Collection {U : Type} (f : nat -> U) : Ensemble U :=
| Collection_intro : forall n, f n ∈ Collection f.
Definition CountableUnion {U : Type} (f : nat -> Ensemble U) : Ensemble U :=
  Union (Collection f).

Check RInt.

Definition is_finite_meas_LInt {A} (f : A -> R+) (μ : FMeas A) (l : R+) : Prop :=
  is_RInt_gen
    (fun t => _r (μ (fun x => _r (f x) > t)))
    (locally 0) (Rbar_locally' p_infty)
    (_r l).