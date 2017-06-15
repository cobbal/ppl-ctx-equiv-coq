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

Lemma fold_apply_paths σ :
  map (flip apply_path σ) = (fun ps => apply_paths ps σ).
Proof.
  reflexivity.
Qed.

Lemma apply_paths_app l0 l1 σ :
  apply_paths (l0 ++ l1) σ = apply_paths l0 σ ++ apply_paths l1 σ.
Proof.
  apply map_app.
Qed.

Fixpoint split_left (p : path) : list path :=
  match p with
  | L :: p' => [p']
  | _ => []
  end.

Fixpoint split_right (p : path) : list path :=
  match p with
  | R :: p' => [p']
  | _ => []
  end.

Definition splits_left := flat_map split_left.
Definition splits_right := flat_map split_right.

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

Fixpoint build_tree n : list path :=
  match n with
  | O => [[]]
  | S n' => map (cons L) (build_tree n') ++ map (cons R) (build_tree n')
  end.

Fixpoint pad_variable n (p : path) : list path :=
  match p, n with
  | [], _ => build_tree n
  | _, O => (* garbage *) []
  | d :: p', S n' => map (cons d) (pad_variable n' p')
  end.

Lemma pad_nil_is_build_tree n :
  pad_variable n [] = build_tree n.
Proof.
  destruct n; auto.
Qed.

Lemma len_build_tree n : length (build_tree n) = 2 ^ n.
Proof.
  induction n; auto.
  cbn.
  rewrite app_length.
  rewrite 2 map_length.
  setoid_rewrite IHn.
  omega.
Qed.

Lemma skipn_length {X} n (l : list X) :
  length (skipn n l) = length l - n.
Proof.
  revert l.
  induction n; destruct l; cbn; auto.
Qed.

Lemma apply_map_cons d l σ :
  apply_paths (map (cons d) l) σ =
  apply_paths l (πd d σ).
Proof.
  induction l; cbn; auto.
  rewrite !fold_apply_paths.
  rewrite IHl.
  reflexivity.
Qed.

Fixpoint join_the_build n (l : list Entropy) : Entropy :=
  match n with
  | O => match l with
         | [σ] => σ
         | _ => dummy_entropy
         end
  | S n' => join (join_the_build n' (firstn (2 ^ n') l))
                 (join_the_build n' (skipn (2 ^ n') l))
  end.

Lemma join_the_build_correct n l :
  length l = 2 ^ n ->
  apply_paths (build_tree n) (join_the_build n l) = l.
Proof.
  revert l.
  induction n; intros. {
    do 2 try destruct l; try discriminate.
    reflexivity.
  } {
    pose proof (IHn (firstn (2 ^ n) l)).
    pose proof (IHn (skipn (2 ^ n) l)).
    clear IHn.

    cbn in *.
    set (σL := join_the_build _ (firstn _ _)) in *.
    set (σR := join_the_build _ (skipn _ _)) in *.
    clearbody σL σR.

    spec1 H0. {
      rewrite firstn_length.
      apply Min.min_l.
      omega.
    }
    spec1 H1. {
      rewrite skipn_length.
      omega.
    }
    clear H.

    rewrite apply_paths_app.
    rewrite 2 apply_map_cons.
    cbn.
    rewrite πL_join, πR_join.
    rewrite H0, H1.
    apply firstn_skipn.
  }
Qed.

Lemma skipn_app {X} n (l0 l1 : list X) :
  length l0 = n ->
  skipn n (l0 ++ l1) = l1.
Proof.
  intros; subst.
  induction l0; auto.
Qed.

Lemma firstn_app_3 {X} n (l0 l1 : list X) :
  length l0 = n ->
  firstn n (l0 ++ l1) = l0.
Proof.
  intros.
  subst.
  replace (length l0) with (length l0 + O) by omega.
  rewrite firstn_app_2.
  cbn.
  apply app_nil_r.
Qed.

Lemma app_len_inj {X} (a a' b b' : list X) :
  length a = length a' ->
  a ++ b = a' ++ b' ->
  a = a' /\ b = b'.
Proof.
  revert a'.
  induction a; destruct a'; try discriminate; intros; auto.
  inject H0.
  cbn in H.
  specialize (IHa a' ltac:(omega) H3).
  inject IHa.
  auto.
Qed.

Definition normalize (Δ : list path) n : list path := flat_map (pad_variable n) Δ.

Fixpoint normalized_lookups (Δ : list path) n (l : list Entropy) : list Entropy :=
  match Δ with
  | [] => l
  | p :: Δ' =>
    (join_the_build (n - length p) (firstn (length (pad_variable n p)) l))
      :: normalized_lookups Δ' n (skipn (length (pad_variable n p)) l)
  end.

Lemma apply_build_tree_injective n :
  Injective (apply_paths (build_tree n)).
Proof.
  hnf.
  induction n; intros. {
    inject H.
    auto.
  } {
    cbn in H.
    rewrite !apply_paths_app, !apply_map_cons in H.
    apply app_len_inj in H; revgoals. {
      setoid_rewrite map_length.
      reflexivity.
    }
    inject H.
    setoid_rewrite <- join_πL_πR.
    cbn in *.
    rewrite (IHn _ _ H0).
    rewrite (IHn _ _ H1).
    reflexivity.
  }
Qed.

Lemma join_of_pad p n :
  length p <= n ->
  forall σ,
    join_the_build (n - length p) (apply_paths (pad_variable n p) σ) =
    apply_path p σ.
Proof.
  revert n.
  induction p; intros. {
    cbn.
    rewrite <- minus_n_O.
    rewrite pad_nil_is_build_tree.

    apply (apply_build_tree_injective n).
    rewrite join_the_build_correct; auto.
    setoid_rewrite map_length.
    apply len_build_tree.
  } {
    cbn in *.
    destruct n; try omega.
    cbn.
    rewrite apply_map_cons.
    apply IHp.
    omega.
  }
Qed.

Lemma normalized_lookups_correct (Δ : list path) n :
  max_list_len Δ <= n ->
  forall σ,
    normalized_lookups Δ n (apply_paths (normalize Δ n) σ) =
    apply_paths Δ σ.
Proof.
  induction Δ; intros. {
    cbn in *.
    reflexivity.
  } {
    pose proof (Max.max_lub_l _ _ _ H).
    spec1 IHΔ. {
      eapply Max.max_lub_r; eauto.
    }
    clear H.

    cbn.
    rewrite fold_apply_paths.
    rewrite apply_paths_app.

    f_equal. {
      rewrite firstn_app_3. {
        apply join_of_pad; auto.
      } {
        setoid_rewrite map_length.
        reflexivity.
      }
    } {
      rewrite skipn_app. {
        apply IHΔ.
      } {
        setoid_rewrite map_length.
        reflexivity.
      }
    }
  }
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

Lemma splits_left_max_len {n Δ} :
  max_list_len Δ <= S n ->
  max_list_len (splits_left Δ) <= n.
Proof.
  revert n.
  induction Δ; intros; cbn in *; try omega.
  rewrite @max_list_len_app.
  apply Max.max_lub; eauto using Max.max_lub_r.
  apply Max.max_lub_l in H.
  induction a as [|[|] ?]; cbn in *; try omega.
  apply Max.max_lub; omega.
Qed.

Lemma splits_right_max_len {n Δ} :
  max_list_len Δ <= S n ->
  max_list_len (splits_right Δ) <= n.
Proof.
  revert n.
  induction Δ; intros; cbn in *; try omega.
  rewrite @max_list_len_app.
  apply Max.max_lub; eauto using Max.max_lub_r.
  apply Max.max_lub_l in H.
  induction a as [|[|]]; cbn in *; try omega.
  apply Max.max_lub; omega.
Qed.

Lemma in_split_left {p p'} :
  In p' (split_left p) ->
  p = L :: p'.
Proof.
  intros.
  destruct p as [|[|]]; cbn in *; intuition idtac.
  subst.
  reflexivity.
Qed.

Lemma in_split_right {p p'} :
  In p' (split_right p) ->
  p = R :: p'.
Proof.
  intros.
  destruct p as [|[|]]; cbn in *; intuition idtac.
  subst.
  reflexivity.
Qed.

Lemma in_splits_left {Δ p} :
  In p (splits_left Δ) ->
  In (L :: p) Δ.
Proof.
  intros.
  induction Δ; auto.
  cbn in *.
  apply in_app_or in H.
  intuition idtac.
  left.
  apply in_split_left; auto.
Qed.

Lemma in_splits_right {Δ p} :
  In p (splits_right Δ) ->
  In (R :: p) Δ.
Proof.
  intros.
  induction Δ; auto.
  cbn in *.
  apply in_app_or in H.
  intuition idtac.
  left.
  apply in_split_right; auto.
Qed.

Lemma splits_left_nondup {Δ} :
  nondup Δ ->
  nondup (splits_left Δ).
Proof.
  induction Δ; intros; auto.
  inject H.
  rewrite Forall_forall in H2.
  cbn.
  apply paths_nondup_app.
  intuition idtac. {
    destruct a as [|[|]]; cbn; auto.
  } {
    apply in_split_left in H0.
    apply in_splits_left in H1.
    subst.
    specialize (H2 _ H1).
    inject H2.
    auto.
  }
Qed.

Lemma splits_right_nondup {Δ} :
  nondup Δ ->
  nondup (splits_right Δ).
Proof.
  induction Δ; intros; auto.
  inject H.
  rewrite Forall_forall in H2.
  cbn.
  apply paths_nondup_app.
  intuition idtac. {
    destruct a as [|[|]]; cbn; auto.
  } {
    apply in_split_right in H0.
    apply in_splits_right in H1.
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

Lemma firstn_map {X Y} n (f : X -> Y) l :
  firstn n (map f l) = map f (firstn n l).
Proof.
  revert l.
  induction n; intros; auto.
  cbn.
  destruct l; cbn; auto.
  rewrite IHn.
  reflexivity.
Qed.

Lemma skipn_all2 {A} n (l : list A) :
  length l <= n ->
  skipn n l = [].
Proof.
  revert n.
  induction l; destruct n; intros; auto. {
    cbn in *.
    omega.
  } {
    cbn in *.
    apply IHl.
    omega.
  }
Qed.

Fixpoint reinterleave (Δ : list path) (σls σrs : list Entropy) : list Entropy :=
  match Δ, σls, σrs with
  | (L :: _) :: Δ', σl :: σls', _ => σl :: reinterleave Δ' σls' σrs
  | (R :: _) :: Δ', _, σr :: σrs' => σr :: reinterleave Δ' σls σrs'
  | _, _, _ => []
  end.

Lemma split_and_reinterleave g Δ :
  ~ In [] Δ ->
  integrate_by_entropies g (length Δ) =
  integrate_by_entropies
    (fun σls =>
       integrate_by_entropies
         (fun σrs =>
            g (reinterleave Δ σls σrs)
         ) (length (splits_right Δ))
    ) (length (splits_left Δ)).
Proof.
  intros.

  revert g.
  induction Δ; intros; auto.

  spec1 IHΔ; destruct a; try (cbn in H; tauto).
  clear H.

  destruct d; cbn. {
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

Lemma integrate_by_entropies_unfold Δ g :
  nondup Δ ->
  integrate_by_entropies g (length Δ) =
  integration (g ∘ apply_paths Δ) μEntropy.
Proof.
  intros.

  unfold compose.
  setoid_rewrite <- normalized_lookups_correct; [| reflexivity].
  remember (max_list_len Δ).

  assert (max_list_len Δ <= n) by omega.
  clear Heqn.

  revert Δ g H H0.
  induction n; intros. {
    destruct Δ as [|? [|]]. {
      cbn in *.
      erewrite int_const_entropy; eauto.
    } {
      destruct p; cbn in *; solve [omega | reflexivity].
    } {
      destruct p as [|[|]], p0 as [|[|]];
        cbn in H, H0;
        destruct max_list_len;
        try omega.
      inject H.
      inject H3.
      inject H2.
    }
  } {
    pose proof (fun Hn HΔ g => IHn (splits_left Δ) g HΔ Hn) as IHL.
    pose proof (fun Hn HΔ g => IHn (splits_right Δ) g HΔ Hn) as IHR.
    clear IHn.

    specialize (IHL (splits_left_max_len H0) (splits_left_nondup H)).
    specialize (IHR (splits_right_max_len H0) (splits_right_nondup H)).

    destruct (in_dec path_eq_dec [] Δ). {
      apply nil_in_nondup in i; auto.
      subst.
      clear.

      integrand_extensionality σ.
      replace (normalize _ _) with (build_tree (S n)) by apply eq_sym, app_nil_r.

      cbn.

      repeat setoid_rewrite firstn_firstn.

      repeat rewrite ?app_length, ?map_length, ?len_build_tree.

      replace (min _ _) with (2 ^ n) by (apply eq_sym, min_l; omega).
      setoid_rewrite firstn_map at 2.
      setoid_rewrite firstn_all2 at 2; revgoals. {
        rewrite app_length, !map_length, !len_build_tree.
        reflexivity.
      }

      setoid_rewrite (join_of_pad [] (S n)); cbn; try omega.

      rewrite skipn_all2; auto.
      setoid_rewrite map_length.
      rewrite app_length, !map_length, !len_build_tree.
      reflexivity.
    } {
      rewrite split_and_reinterleave; auto.
      rewrite IHL.
      setoid_rewrite IHR.
      clear IHL IHR.
      rewrite <- integration_πL_πR.

      integrand_extensionality σ.

      rewrite 3 normalized_lookups_correct; auto; revgoals. {
        apply splits_left_max_len; auto.
      } {
        apply splits_right_max_len; auto.
      }

      f_equal.
      clear H H0 n g.

      induction Δ; intros; auto.

      spec1 IHΔ; [cbn in *; tauto |].
      destruct a; [cbn in *; tauto |].

      destruct d; cbn; f_equal; apply IHΔ.
    }
  }
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
  rewrite <- 2 integrate_by_entropies_unfold; try assumption.
  rewrite H1.
  reflexivity.
Qed.