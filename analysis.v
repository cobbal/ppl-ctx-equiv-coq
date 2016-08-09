(* Add LoadPath "Topology". *)
Add LoadPath "ZornsLemma" as ZornsLemma.

Require Import Reals.
Require Import List.
Require Import Fourier.
Require Import Basics.
Require Import Ensembles.
Require Import ZornsLemma.IndexedFamilies.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Notation "∅" := Empty_set.
Notation "x ∈ X" := (In X x) (at level 80, no associativity).
Notation "x ∉ X" := (~ In X x) (at level 80, no associativity).
Notation " g ∘ f " := (compose g f)
  (at level 40, left associativity).
Definition preimage {A B} (f : A -> B) : Ensemble B -> Ensemble A :=
  fun bs a => f a ∈ bs.

Module Type σAlgebra.
  Parameter X : Type.
  Parameter Σ : Family X.
  Parameter Σ_dec : forall x σ, σ ∈ Σ -> {x ∈ σ} + {x ∉ σ}.

  Axiom contains_empty : ∅ ∈ Σ.
  Axiom closed_comp : forall σ, σ ∈ Σ -> Ensembles.Complement σ ∈ Σ.
  Axiom closed_union : forall σ0 σ1, σ0 ∈ Σ -> σ1 ∈ Σ -> Union σ0 σ1 ∈ Σ.
  Axiom closed_countable_union : forall F : IndexedFamily nat X,
      (forall n, F n ∈ Σ) ->
      IndexedUnion F ∈ Σ.

End σAlgebra.

Inductive eNNR :=
| NNR : nonnegreal -> eNNR
| Infty : eNNR.

Program Definition eNNR_plus (a b : eNNR) : eNNR :=
  match (a, b) with
  | (NNR a', NNR b') => NNR (mknonnegreal (a' + b') _)
  | (Infty, _) => Infty
  | (_, Infty) => Infty
  end.
Next Obligation.
  destruct_all nonnegreal.
  simpl.
  fourier.
Qed.

Program Definition eNNR_leq (a b : eNNR) : Prop :=
  match (a, b) with
  | (NNR a', NNR b') => a' <= b'
  | (Infty, NNR b') => False
  | (_, Infty) => True
  end.

Notation "x ≤ y" := (eNNR_leq x y) (at level 70, no associativity).


Program Definition eNNR_0 := NNR (mknonnegreal 0 _).
Solve Obligations with fourier.

Program Definition NNR_eNNR_mult (a : nonnegreal) (b : eNNR) : eNNR :=
  if Req_EM_T a 0
  then eNNR_0
  else match (a, b) with
       | (a', NNR b') => NNR (mknonnegreal (a' * b') _)
       | (_, Infty) => Infty
       end.
Next Obligation.
  apply Rmult_le_pos; destruct_all nonnegreal; auto.
Qed.

Axiom infinite_eNNR_sum : (nat -> eNNR) -> eNNR.
Axiom eNNR_sup : forall {A}, (A -> eNNR) -> eNNR.

Module Type Measure (σAlg : σAlgebra).
  Import σAlg.

  Parameter μ : forall σ, σ ∈ Σ -> eNNR.

  Axiom null_empty : forall p, μ ∅ p = eNNR_0.

  Axiom countable_additivity :
    forall (E : IndexedFamily nat X)
           (p0 : forall n, E n ∈ Σ)
           p1,
      (forall i j, i <> j -> Disjoint (E i) (E j)) ->
      infinite_eNNR_sum (fun x => μ (E x) (p0 x)) = μ (IndexedUnion E) p1.

  (* Program Definition Indicator (σ : Ensemble X) (_ : σ ∈ Σ) (x : X) : eNNR := *)
  (*            NNR (mknonnegreal (if Σ_dec x σ _ then 1 else 0) _) . *)
  (* Solve Obligations using intuition; induction Σ_dec; fourier. *)

  Definition R_lt_eNNR (a : R) (b : eNNR) : Prop :=
    match b with
    | NNR r => a < r
    | Infty => False
    end.

  Definition Measurable (f : X -> eNNR) : Prop :=
    forall t : R, preimage f (R_lt_eNNR t) ∈ Σ.

  Definition SimpleFn := list (nonnegreal * {σ : Ensemble X | σ ∈ Σ}).

  Fixpoint SimpleEval (f : SimpleFn) (x : X) : eNNR :=
    match f with
    | nil => eNNR_0
    | cons (a, i) f' => eNNR_plus
                          (if Σ_dec x (proj1_sig i) (proj2_sig i) then NNR a else eNNR_0)
                          (SimpleEval f' x)
    end.

  Fixpoint SimpleInt (s : SimpleFn) : eNNR :=
    match s with
      | nil => eNNR_0
      | cons (a, i) s' => eNNR_plus (NNR_eNNR_mult a (μ (proj1_sig i) (proj2_sig i)))
                          (SimpleInt s')
    end.

  Definition NNInt f : Measurable f -> eNNR :=
    fun f_mbl =>
      eNNR_sup
        (fun sp : {s : SimpleFn |
                   forall x,
                      eNNR_0 ≤ SimpleEval s x /\
                      SimpleEval s x ≤ f x} =>
           SimpleInt (proj1_sig sp)).

  Theorem simple_is_measurable :
    forall s : SimpleFn,
      Measurable (SimpleEval s).
  Proof.
    intros.
    intro.
    induction s. {
      assert (SimpleEval nil = const eNNR_0) by auto.
      rewrite H.
      clear H.
      unfold preimage, const.
      unfold In at 2.

      unfold R_lt_eNNR.
      unfold eNNR_0.
      simpl.

      induction (Rlt_dec t 0). {
        rewrite (Extensionality_Ensembles (fun _ : X => t < 0) (Ensembles.Complement ∅)). {
          exact (closed_comp _ contains_empty).
        } {
          split; unfold Included; intros x _; auto.
          intro H.
          case H.
        }
      } {
        rewrite (Extensionality_Ensembles (fun _ : X => t < 0) ∅). {
          exact contains_empty.
        } {
          split; unfold Included; intros x H; contradict H; auto.
        }
      }
    } {
      destruct a as [n [σ Hσ]].
      simpl.
      unfold preimage in *.
    }


  Qed.

  Theorem NNInt_extends_SimpleInt :
    forall s : SimpleFn,
      SimpleInt s = NNInt (SimpleEval s) _.
