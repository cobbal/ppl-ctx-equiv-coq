(** Entropy is the source of all randomness in an evaluation. The particular
    representation we choose is the Hilbert cube #(ℕ → [0, 1])#. In particular,
    the properties we use on it are that an entropy source can be split into two
    entropy sources through the operations [πL] and [πR], which are defined here
    and axiomatized to be IID in [integration_πL_πR]. When it actually comes to
    using an entropy [σ], it is also convenient to split it into arbitrarily
    many indepent parts, as (π 0 σ), (π 1 σ), ... *)

Require Import Reals.
Require Import utils.

Local Open Scope R.

Definition Entropy := nat -> {r : R | 0 <= r <= 1}.

(** The projection functions don't muck with any real numbers, just shuffle
    indices around. [πL_n] and the like are the exact index shuffling needed for
    [πL] and the like. *)
Definition πL_n : nat -> nat := fun n => (n + n)%nat.
Definition πR_n : nat -> nat := fun n => S (n + n)%nat.

(** [join] is the inverse of projections, that is [σ = join (πL σ) (πR σ)]. This
    is later proved as [join_πL_πR]. This is finally automated in the tactic
    [π_join]. *)
Definition join' {A} (L R : nat -> A) : nat -> A :=
  fun n =>
    if Nat.even n
    then L (Nat.div2 n)
    else R (Nat.div2 n).

Definition πL (σ : Entropy) : Entropy := σ ∘ πL_n.
Definition πR (σ : Entropy) : Entropy := σ ∘ πR_n.
Definition join : Entropy -> Entropy -> Entropy := join'.

Lemma πL_join σL σR : πL (join σL σR) = σL.
Proof.
  extensionality n.
  unfold πL, πL_n, join, join', compose.
  assert (Nat.even (n + n) = true). {
    induction n; simpl; auto.
    replace (n + S n)%nat with (S (n + n)); auto.
  }
  rewrite H.
  f_equal.
  fold (Nat.double n).
  rewrite Nat.double_twice.
  apply Nat.div2_double.
Qed.

Lemma πR_join σL σR : πR (join σL σR) = σR.
Proof.
  extensionality n.
  unfold πR, πR_n, join, join', compose.
  assert (Nat.even (S (n + n)) = false). {
    induction n; simpl; auto.
    replace (n + S n)%nat with (S (n + n)); auto.
  }
  rewrite H.
  f_equal.
  fold (Nat.double n).
  rewrite Nat.double_twice.
  apply Nat.div2_succ_double.
Qed.

Lemma join_πL_πR σ : join (πL σ) (πR σ) = σ.
Proof.
  extensionality n.
  unfold join, join', πL, πR, πL_n, πR_n, compose.
  destruct (Nat.Even_or_Odd n). {
    rewrite (proj2 (Nat.even_spec n)); auto.

    f_equal.
    fold (Nat.double (Nat.div2 n)).
    rewrite <- Div2.even_double; auto.
    apply Even.even_equiv; auto.
  } {
    pose proof (proj2 (Nat.odd_spec n) H).
    rewrite <- Nat.negb_even in H0.
    apply Bool.negb_true_iff in H0.
    rewrite H0.

    f_equal.
    change (S (Nat.double (Nat.div2 n)) = n).
    rewrite <- Div2.odd_double; auto.
    apply Even.odd_equiv; auto.
  }
Qed.

Fixpoint π (n : nat) (σ : Entropy) : Entropy :=
  match n with
  | O => πL σ
  | S n' => π n' (πR σ)
  end.
Arguments π _ _ _ : simpl never.

Fixpoint π_leftover (n : nat) (σ : Entropy) : Entropy :=
  match n with
  | O => σ
  | S n' => π_leftover n' (πR σ)
  end.
Arguments π_leftover _ _ _ : simpl never.

Lemma π_O_join (σl σr : Entropy) : π 0 (join σl σr) = σl.
Proof.
  apply πL_join.
Qed.

Lemma π_S_join (n : nat) (σl σr : Entropy) : π (S n) (join σl σr) = π n σr.
Proof.
  unfold π.
  fold π.
  rewrite πR_join.
  auto.
Qed.

Ltac π_join := repeat rewrite ?π_O_join, ?π_S_join in *.
