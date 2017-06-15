Require Import utils.
Require Import integration.
Require Import entropy.
Require Import List.
Require Import Omega.
Require Import FinFun.

Import ListNotations.

Open Scope nat.
Open Scope list.

Arguments id {_} _ /.
Arguments flip {_ _ _} _ _ _ /.
Arguments Datatypes.id {_} _ /.

Inductive dir := L | R.
Definition πd (d : dir) := if d then πL else πR.

Definition path := list dir.

Lemma dir_eq_dec (d0 d1 : dir) : {d0 = d1} + {d0 <> d1}.
Proof.
  decide equality.
Qed.

Definition path_eq_dec : forall (p0 p1 : path), {p0 = p1} + {p0 <> p1}
  := list_eq_dec (dir_eq_dec).

Ltac spec1 H :=
  let H' := fresh "H" in
  lazymatch type of H with
  | ?A -> ?B =>
    assert (H' : A);
    [try clear H | specialize (H H'); try clear H']
  | forall x : ?A, ?B =>
    simple refine (let H' : A := _ in _);
      [try clear H | specialize (H H'); subst H']
  end.

(** "neither is a prefix of the other" *)
Inductive paths_disjoint : path -> path -> Prop :=
| disjoint_LR p0 p1 : paths_disjoint (L :: p0) (R :: p1)
| disjoint_RL p0 p1 : paths_disjoint (R :: p0) (L :: p1)
| disjoint_tail d p0 p1 : paths_disjoint p0 p1 -> paths_disjoint (d :: p0) (d :: p1)
.
Hint Constructors paths_disjoint.

Fixpoint apply_path (p : path) : Entropy -> Entropy :=
  match p with
  | [] => id
  | d :: p' => apply_path p' ∘ πd d
  end.

Inductive nondup : list path -> Prop :=
| nondup_nil : nondup []
| nondup_cons p ps :
    Forall (paths_disjoint p) ps ->
    nondup ps ->
    nondup (p :: ps)
.
Hint Constructors nondup.

Lemma paths_nondup_app (l0 l1 : list path) :
  (nondup l0 /\
   nondup l1 /\
   (forall p0 p1, In p0 l0 -> In p1 l1 -> paths_disjoint p0 p1)) <->
  nondup (l0 ++ l1).
Proof.
  induction l0. {
    cbn.
    intuition eauto.
  } {
    split; intros. {
      destruct IHl0 as [? _].
      intuition idtac.
      inject H1.
      intuition idtac.
      cbn in *.

      constructor; eauto.
      apply Forall_forall.
      rewrite Forall_forall in H5.
      intros.
      apply in_app_or in H1.
      inject H1; eauto.
    } {
      destruct IHl0 as [_ ?].
      inject H.
      cbn in *.
      rewrite Forall_forall in H3.
      intuition idtac; eauto. {
        constructor; eauto.
        rewrite Forall_forall.
        intros.
        eapply H3; eauto.
        apply in_or_app; auto.
      } {
        subst.
        apply H3.
        apply in_or_app; auto.
      }
    }
  }
Qed.

Definition apply_paths (ps : list path) (σ : Entropy) : list Entropy :=
  map (flip apply_path σ) ps.
Arguments apply_paths !_ _.

Fixpoint split (d : dir) (p : path) : list path :=
  match d, p with
  | L, L :: p' => [p']
  | R, R :: p' => [p']
  | _, _ => []
  end.

Definition splits := fun d => flat_map (split d).

Fixpoint integrate_by_entropies (g : list Entropy -> R+) (n : nat) : R+ :=
  match n with
  | O => g []
  | S n' => integration (fun σ => integrate_by_entropies (fun σs => g (σ :: σs)) n') μEntropy
  end.

Fixpoint max_list_len {X} (l : list (list X)) :=
  match l with
  | [] => 0
  | b :: bs => max (length b) (max_list_len bs)
  end.

Lemma max_list_len_app {X} (l0 l1 : list (list X)) :
  max_list_len (l0 ++ l1) = max (max_list_len l0) (max_list_len l1).
Proof.
  induction l0; auto.
  cbn.
  rewrite IHl0.
  apply Nat.max_assoc.
Qed.

Lemma tonelli_entropies_and_entropy n (f : list Entropy -> Entropy -> R+) :
  integrate_by_entropies (fun σs => integration (fun σ => f σs σ) μEntropy) n =
  integration (fun σ => integrate_by_entropies (fun σs => f σs σ) n) μEntropy.
Proof.
  revert f.
  induction n; intros; auto.
  cbn.
  rewrite tonelli_sigma_finite; auto.
  setoid_rewrite IHn.
  reflexivity.
Qed.

Lemma splits_max_len {n Δ} :
  max_list_len Δ <= S n ->
  forall d,
    max_list_len (splits d Δ) <= n.
Proof.
  revert n.
  induction Δ; intros; cbn in *; try omega.
  rewrite @max_list_len_app.
  apply Max.max_lub; eauto using Max.max_lub_r.
  apply Max.max_lub_l in H.
  induction a as [| [|] ?];
    destruct d;
    cbn in *;
    try apply Max.max_lub;
    omega.
Qed.

Lemma splits_max_len' {Δ} :
  0 <> max_list_len Δ ->
  forall d,
    max_list_len (splits d Δ) < max_list_len Δ.
Proof.
  intros.
  unfold lt.
  remember (max_list_len Δ).
  destruct n; try omega.
  apply le_n_S.
  apply splits_max_len.
  rewrite Heqn.
  reflexivity.
Qed.

Lemma in_split {p p' d} :
  In p' (split d p) ->
  p = d :: p'.
Proof.
  intros.
  destruct d, p as [|[|]];
    cbn in *;
    intuition (subst; trivial).
Qed.

Lemma in_splits {Δ p d} :
  In p (splits d Δ) ->
  In (d :: p) Δ.
Proof.
  intros.
  induction Δ; auto.
  cbn in *.
  apply in_app_or in H.
  intuition idtac.
  left.
  apply in_split; auto.
Qed.

Lemma splits_nondup {Δ} :
  nondup Δ ->
  forall d,
    nondup (splits d Δ).
Proof.
  intros.
  induction Δ; intros; auto.
  inject H.
  rewrite Forall_forall in H2.
  cbn.
  apply paths_nondup_app.
  intuition idtac. {
    destruct d, a as [|[|]]; cbn; auto.
  } {
    apply in_split in H0.
    apply in_splits in H1.
    subst.
    specialize (H2 _ H1).
    inject H2.
    auto.
  }
Qed.

Lemma nil_in_nondup Δ :
  nondup Δ ->
  In [] Δ ->
  Δ = [[]].
Proof.
  intros.
  destruct Δ; try tauto.
  inject H.
  destruct p. {
    destruct Δ; auto.
    inject H3.
    inject H2.
  }
  exfalso.
  inject H0; try discriminate.
  rewrite Forall_forall in H3.
  specialize (H3 _ H).
  inject H3.
Qed.

Fixpoint reinterleave (Δ : list path) (σls σrs : list Entropy) : list Entropy :=
  match Δ, σls, σrs with
  | (L :: _) :: Δ', σl :: σls', _ => σl :: reinterleave Δ' σls' σrs
  | (R :: _) :: Δ', _, σr :: σrs' => σr :: reinterleave Δ' σls σrs'
  | _, _, _ => []
  end.

Lemma reinterleave_splits Δ σ :
  ~ In [] Δ ->
  reinterleave Δ (apply_paths (splits L Δ) (πL σ)) (apply_paths (splits R Δ) (πR σ)) =
  apply_paths Δ σ.
Proof.
  revert σ.
  induction Δ; intros; auto.

  apply not_in_cons in H.
  inject H.
  destruct a; try contradiction.

  transitivity (apply_path a (πd d σ) :: apply_paths Δ σ); auto.
  rewrite <- IHΔ; auto.
  destruct d; reflexivity.
Qed.

Lemma split_and_reinterleave g Δ :
  ~ In [] Δ ->
  integrate_by_entropies g (length Δ) =
  integrate_by_entropies
    (fun σls =>
       integrate_by_entropies
         (fun σrs =>
            g (reinterleave Δ σls σrs)
         ) (length (splits R Δ))
    ) (length (splits L Δ)).
Proof.
  intros.

  revert g.
  induction Δ; intros; auto.

  apply not_in_cons in H.
  inject H.

  spec1 IHΔ; auto.

  destruct a as [|[|] ?]; cbn; try contradiction. {
    integrand_extensionality σ.
    rewrite IHΔ.
    reflexivity.
  } {
    rewrite tonelli_entropies_and_entropy.
    integrand_extensionality σ.
    rewrite IHΔ.
    reflexivity.
  }
Qed.

(* inspired by https://stackoverflow.com/questions/20883855 *)
Theorem strong_induction (P : nat -> Type) :
  (forall n, (forall k, k < n -> P k) -> P n) ->
  forall n, P n.
Proof.
  intros H n.
  apply H.
  induction n; intros. {
    omega.
  } {
    apply H.
    intros.
    apply IHn.
    omega.
  }
Qed.

Lemma integrate_by_entropies_unfold Δ g :
  nondup Δ ->
  integration (g ∘ apply_paths Δ) μEntropy =
  integrate_by_entropies g (length Δ).
Proof.
  intros.

  remember (max_list_len Δ) as m.
  revert Δ Heqm H g.
  induction m using strong_induction.
  intros; subst.
  specialize (fun Δ' Hk => H _ Hk Δ' eq_refl).

  destruct (list_eq_dec path_eq_dec Δ []). {
    subst.
    apply int_const_entropy; auto.
  }

  destruct (in_dec path_eq_dec [] Δ) as [?H | ?H]. {
    rewrite (nil_in_nondup Δ); try assumption.
    reflexivity.
  }

  rewrite split_and_reinterleave; auto.

  assert (0 <> max_list_len Δ). {
    destruct Δ as [|[|] Δ]; cbn in *; try tauto.
    destruct (max_list_len Δ); discriminate.
  }

  pose proof splits_nondup H0.
  pose proof splits_max_len' H2.

  do 2 (setoid_rewrite <- H; auto).

  unfold compose.
  rewrite <- integration_πL_πR.
  integrand_extensionality σ.

  rewrite reinterleave_splits; auto.
Qed.

Lemma diagram (Δ Δ' : list path) (f f' : Entropy -> R+) (g : list Entropy -> R+) :
  nondup Δ ->
  nondup Δ' ->
  length Δ = length Δ' ->
  f = g ∘ apply_paths Δ ->
  f' = g ∘ apply_paths Δ' ->
  integration f μEntropy = integration f' μEntropy.
Proof.
  intros.
  subst.
  rewrite 2 integrate_by_entropies_unfold; try assumption.
  rewrite H1.
  reflexivity.
Qed.