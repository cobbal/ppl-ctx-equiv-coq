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

Lemma tonelli_entropy {A} (f : Entropy -> Entropy -> Meas A) :
  μEntropy >>= (fun x0 => μEntropy >>= (fun x1 => f x0 x1)) =
  μEntropy >>= (fun x1 => μEntropy >>= (fun x0 => f x0 x1)).
Proof.
  extensionality ev.
  apply tonelli_sigma_finite; auto.
Qed.

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
Fixpoint path_conflict (p0 p1 : path) : Prop :=
  match p0, p1 with
  | [], _ | _, [] => True
  | L :: _, R :: _ => False
  | R :: _, L :: _ => False
  | _ :: p0', _ :: p1' => path_conflict p0' p1'
  end.

Inductive FTF :=
| Leaf (l : path)
| Node (tL tR : FTF)
.

Infix ";;" := Node (at level 60, right associativity).

Fixpoint conflicts_in (p : path) (f : FTF) : Prop :=
  match f with
  | Leaf l => path_conflict p l
  | Node tL tR => conflicts_in p tL \/ conflicts_in p tR
  end.

Fixpoint vars_of (f : FTF) : list path :=
  match f with
  | Leaf l => [l]
  | Node tL tR => vars_of tL ++ vars_of tR
  end.

Inductive nondup : FTF -> Prop :=
| nondup_leaf l : nondup (Leaf l)
| nondup_node tL tR :
    nondup tL ->
    nondup tR ->
    (forall pL pR, In pL (vars_of tL) -> In pR (vars_of tR) -> ~ path_conflict pL pR) ->
    nondup (tL ;; tR).

Lemma path_conflict_sym l0 l1 :
  path_conflict l0 l1 <-> path_conflict l1 l0.
Proof.
  revert l1.
  induction l0; intros. {
    induction l1; cbn in *; try tauto.
    destruct a; tauto.
  } {
    destruct a. {
      induction l1; cbn; try tauto.
      destruct a; try tauto.
      apply IHl0.
    } {
      induction l1; cbn; try tauto.
      destruct a; try tauto.
      apply IHl0.
    }
  }
Qed.

Lemma conflicts_in_reflected_by_path_conflict f p l :
  In p (vars_of f) ->
  path_conflict l p ->
  conflicts_in l f.
Proof.
  reverse.
  induction f; intros. {
    inject H; tauto.
  } {
    cbn in *.
    apply in_app_or in H.
    inject H; eauto.
  }
Qed.

Fixpoint apply_path (p : path) : Entropy -> Entropy :=
  match p with
  | [] => id
  | d :: p' => apply_path p' ∘ πd d
  end.

Fixpoint apply_FTF (f : FTF) (σ : Entropy) : Entropy :=
  match f with
  | Leaf l => apply_path l σ
  | fL ;; fR => join (apply_FTF fL σ) (apply_FTF fR σ)
  end.

Record good (f : FTF) :=
  mk_good {
      good_nondup : nondup f;
      good_pushforward : pushforward μEntropy (apply_FTF f) = μEntropy;
    }.

Definition comm_FTF : FTF :=
  Leaf [R] ;; Leaf [L].
Definition let_comm_FTF : FTF :=
  Leaf [R; L] ;; Leaf [L] ;; Leaf [R; R].
Definition assoc_l_FTF : FTF :=
  (Leaf [L] ;; Leaf [R; L]) ;; Leaf [R; R].
Definition assoc_r_FTF : FTF :=
  Leaf [L; L] ;; Leaf [L; R] ;; Leaf [R].
Definition πR_FTF : FTF := Leaf [R].

Ltac show_concrete_nondup :=
  repeat constructor;
  cbn;
  intros;
  intuition (subst; auto).

Lemma comm_good : good comm_FTF.
  split. {
    show_concrete_nondup.
  } {
    hnf.
    rewrite pushforward_as_bind; cbn.
    unfold compose, id, Datatypes.id.
    setoid_rewrite (bind_πL_πR (fun σL σR => dirac (join σR σL))).

    setoid_rewrite tonelli_entropy.
    setoid_rewrite <- bind_πL_πR.
    setoid_rewrite join_πL_πR.
    apply meas_id_right.
  }
Qed.

Lemma let_comm_good : good let_comm_FTF.
Proof.
  split. {
    show_concrete_nondup.
  } {
    hnf.
    rewrite pushforward_as_bind; cbn.
    unfold compose, id, Datatypes.id.
    setoid_rewrite (bind_πL_πR (fun σL σR => dirac (join (πL σR) (join σL (πR σR))))).
    setoid_rewrite (bind_πL_πR (fun σLR σRR => dirac (join σLR (join _ σRR)))).

    setoid_rewrite tonelli_entropy at 2.
    setoid_rewrite <- bind_πL_πR.
    setoid_rewrite join_πL_πR.

    setoid_rewrite tonelli_entropy.
    setoid_rewrite <- bind_πL_πR.
    setoid_rewrite join_πL_πR.
    apply meas_id_right.
  }
Qed.

Lemma assoc_l_good : good assoc_l_FTF.
Proof.
  split. {
    show_concrete_nondup.
  } {
    hnf.
    rewrite pushforward_as_bind; cbn.
    unfold compose, id, Datatypes.id.

    setoid_rewrite (bind_πL_πR (fun σL σR => dirac (join (join σL (πL σR)) (πR σR)))).
    setoid_rewrite (bind_πL_πR (fun σLR σRR => dirac (join (join _ σLR) σRR))).

    setoid_rewrite <- bind_πL_πR.
    setoid_rewrite join_πL_πR.
    setoid_rewrite <- bind_πL_πR.
    setoid_rewrite join_πL_πR.
    apply meas_id_right.
  }
Qed.

Lemma assoc_r_good : good assoc_r_FTF.
Proof.
  split. {
    show_concrete_nondup.
  } {
    hnf.
    rewrite pushforward_as_bind; cbn.
    unfold compose, id, Datatypes.id.

    setoid_rewrite (bind_πL_πR (fun σL σR => dirac (join (πL σL) (join (πR σL) σR)))).
    rewrite tonelli_entropy.
    setoid_rewrite (bind_πL_πR (fun σLL σRL => dirac (join σLL (join σRL _)))).

    setoid_rewrite tonelli_entropy at 1.
    setoid_rewrite tonelli_entropy at 2.
    setoid_rewrite <- bind_πL_πR at 2.
    setoid_rewrite join_πL_πR.
    setoid_rewrite <- bind_πL_πR.
    setoid_rewrite join_πL_πR.
    apply meas_id_right.
  }
Qed.

Lemma πL_good : good πR_FTF.
Proof.
  split. {
    show_concrete_nondup.
  } {
    hnf.
    rewrite pushforward_as_bind; cbn.
    unfold compose, id, Datatypes.id.

    setoid_rewrite (bind_πL_πR (fun _ σR => dirac σR)).
    rewrite meas_id_right.
    extensionality A.
    apply int_const_entropy; auto.
  }
Qed.

Fixpoint paths_nondup (ps : list path) : Prop :=
  match ps with
  | nil => True
  | p :: ps' => Forall (fun p' => ~ path_conflict p p') ps' /\ paths_nondup ps'
  end.

Lemma paths_nondup_app (l0 l1 : list path) :
  (paths_nondup l0 /\
   paths_nondup l1 /\
   (forall p0 p1, In p0 l0 -> In p1 l1 -> ~ path_conflict p0 p1)) <->
  paths_nondup (l0 ++ l1).
Proof.
  intros.
  induction l0. {
    cbn.
    intuition idtac.
  } {
    split; intros. {
      destruct IHl0 as [? _].
      intuition idtac.
      cbn in H1.
      intuition idtac.

      cbn.
      split. {
        apply Forall_forall.
        intros.
        apply in_app_or in H2.
        rewrite Forall_forall in H0.
        inject H2; eauto.
        intro.
        eapply H3; eauto.
        left; auto.
      } {
        apply H1.
        intros.
        eapply H3; eauto.
        right; auto.
      }
    } {
      destruct IHl0 as [_ ?].
      cbn in H.
      rewrite Forall_forall in H.
      intuition idtac. {
        cbn.
        split; auto.
        rewrite Forall_forall.
        repeat intro.
        eapply H1; eauto.
        apply in_or_app; auto.
      } {
        inject H3. {
          specialize (H1 p1).
          apply H1; auto.
          apply in_or_app; auto.
        } {
          eapply H4; eauto.
        }
      }
    }
  }
Qed.

Lemma nondup_is_vars_nondup (f : FTF) :
  nondup f <-> paths_nondup (vars_of f).
Proof.
  induction f. {
    repeat split; constructor.
  } {
    intuition idtac. {
      inject H3.
      intuition idtac.
      clear H6 H7.
      cbn.
      apply paths_nondup_app; auto.
    } {
      cbn in H3.
      apply paths_nondup_app in H3.
      intuition idtac.
      clear H H2.
      constructor; auto.
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

Lemma integrate_by_entropies_n_ext f g n :
  (forall l, length l = n -> f l = g l) ->
  integrate_by_entropies f n = integrate_by_entropies g n.
Proof.
  revert f g.
  induction n; intros. {
    intros.
    cbn.
    rewrite H; auto.
  } {
    intros.
    cbn.
    integrand_extensionality σ.
    apply IHn.
    intros.
    apply H.
    subst.
    auto.
  }
Qed.

Lemma integrate_by_entropies_nest g n n' :
  integrate_by_entropies g (n + n') =
  integrate_by_entropies
    (fun l =>
       integrate_by_entropies
         (fun l' => g (l ++ l')) n') n.
Proof.
  revert g.
  induction n; intros; cbn; auto.
  integrand_extensionality σ.
  apply IHn.
Qed.

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

Lemma apply_dep_cons d l σ :
  apply_paths (map (cons d) l) σ =
  apply_paths l (πd d σ).
Proof.
  induction l; cbn; auto.
  setoid_rewrite IHl.
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

    setoid_rewrite apply_paths_app.
    setoid_rewrite map_map.
    cbn.
    rewrite πL_join, πR_join.
    setoid_rewrite H0.
    setoid_rewrite H1.
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
  apply app_nil_r.
Qed.

Lemma app_len_inj {X} (a a' b b' : list X) :
  length a = length a' ->
  a ++ b = a' ++ b' ->
  a = a' /\ b = b'.
Proof.
  revert a'.
  induction a; destruct a'; try discriminate; intros; auto.
  cbn in *.
  inject H0.
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
    cbn -[apply_paths] in H.
    rewrite !apply_paths_app, !apply_dep_cons in H.
    apply app_len_inj in H; revgoals. {
      repeat setoid_rewrite map_length.
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
    repeat setoid_rewrite map_length.
    apply len_build_tree.
  } {
    cbn in *.
    destruct n; try omega.
    cbn -[apply_paths].
    rewrite apply_dep_cons.
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

    simpl.
    setoid_rewrite apply_paths_app.

    rewrite skipn_app; revgoals. {
      repeat setoid_rewrite map_length.
      reflexivity.
    }
    rewrite firstn_app_3; revgoals. {
      repeat setoid_rewrite map_length.
      reflexivity.
    }

    rewrite join_of_pad; auto.
    rewrite IHΔ.
    reflexivity.
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
  setoid_rewrite max_list_len_app.
  apply Max.max_lub; eauto using Max.max_lub_r.
  apply Max.max_lub_l in H.
  induction a as [|[|]]; cbn in *; try omega.
  apply Max.max_lub; omega.
Qed.

Lemma splits_right_max_len {n Δ} :
  max_list_len Δ <= S n ->
  max_list_len (splits_right Δ) <= n.
Proof.
  revert n.
  induction Δ; intros; cbn in *; try omega.
  setoid_rewrite max_list_len_app.
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
  paths_nondup Δ ->
  paths_nondup (splits_left Δ).
Proof.
  induction Δ; intros; auto.
  replace (a :: Δ) with ([a] ++ Δ) in * by auto.
  apply paths_nondup_app in H.
  cbn.
  apply paths_nondup_app.
  intuition idtac. {
    destruct a as [|[|]]; cbn; auto.
  } {
    apply in_split_left in H3.
    apply in_splits_left in H4.
    subst.
    specialize (H2 (L :: p0) (L :: p1) ltac:(cbn; auto) H4).
    cbn in H2.
    auto.
  }
Qed.

Lemma splits_right_nondup {Δ} :
  paths_nondup Δ ->
  paths_nondup (splits_right Δ).
Proof.
  induction Δ; intros; auto.
  replace (a :: Δ) with ([a] ++ Δ) in * by auto.
  apply paths_nondup_app in H.
  cbn.
  apply paths_nondup_app.
  intuition idtac. {
    destruct a as [|[|]]; cbn; auto.
  } {
    apply in_split_right in H3.
    apply in_splits_right in H4.
    subst.
    specialize (H2 (R :: p0) (R :: p1) ltac:(cbn; auto) H4).
    cbn in H2.
    auto.
  }
Qed.

Lemma nil_in_nondup Δ :
  paths_nondup Δ ->
  In [] Δ ->
  Δ = [[]].
Proof.
  intros.
  destruct Δ; try tauto.
  inject H.
  destruct p. {
    destruct Δ; auto.
    cbn in H1.
    inject H1.
    tauto.
  }
  exfalso.
  inject H0; try discriminate.
  rewrite Forall_forall in H1.
  eapply H1; eauto.
  cbn.
  destruct d; trivial.
Qed.

Lemma firstn_map {X Y} n (f : X -> Y) l :
  firstn n (map f l) = map f (firstn n l).
Proof.
  revert l.
  induction n; intros; auto.
  cbn.
  destruct l; cbn; auto.
  f_equal.
  apply IHn.
Qed.

Lemma skipn_all2 {A} n (l : list A) :
  length l <= n ->
  skipn n l = [].
Proof.
  intros.
  revert n H.
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
  spec1 IHΔ; [cbn in *; tauto|].

  destruct a; cbn in H; try tauto.

  destruct d; cbn in *. {
    setoid_rewrite IHΔ.
    reflexivity.
  } {
    setoid_rewrite IHΔ.
    rewrite tonelli_entropies_and_entropy.
    reflexivity.
  }
Qed.

Lemma integrate_by_entropies_unfold Δ g :
  paths_nondup Δ ->
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
    destruct Δ as [|? [|]]; swap 2 3. {
      cbn in *.
      erewrite int_const_entropy; eauto.
    } {
      destruct p as [|[|]], p0 as [|[|]];
        cbn in H, H0;
        destruct max_list_len;
        try omega.
      inject H.
      inject H1.
      tauto.
    } {
      destruct p; cbn in *; try omega.
      reflexivity.
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
      cbn.

      pose proof (join_of_pad [] (S n) ltac:(cbn; omega)).
      cbn in *.
      repeat setoid_rewrite firstn_firstn.

      repeat rewrite ?app_length, ?map_length, ?len_build_tree.
      rewrite app_nil_r.

      set (min _ _).
      replace n0 with (2 ^ n); subst n0; revgoals. {
        symmetry.
        apply min_l.
        omega.
      }

      setoid_rewrite firstn_map at 2.
      setoid_rewrite firstn_all2 at 2; revgoals. {
        rewrite app_length, !map_length, !len_build_tree.
        reflexivity.
      }
      setoid_rewrite H.
      clear H.

      rewrite skipn_all2; auto.
      setoid_rewrite map_length.
      rewrite app_length, !map_length, !len_build_tree.
      reflexivity.
    }

    rewrite split_and_reinterleave; auto.
    rewrite IHL.
    setoid_rewrite IHR.
    clear IHL IHR.
    rewrite <- integration_πL_πR.

    integrand_extensionality σ.

    repeat rewrite normalized_lookups_correct; auto; revgoals. {
      apply splits_left_max_len; auto.
    } {
      apply splits_right_max_len; auto.
    }

    f_equal.
    clear H H0 n g.

    induction Δ; intros; auto.
    assert (~ In [] Δ) by (cbn in *; tauto).

    destruct a; cbn in *; try tauto.

    destruct d; cbn; f_equal; apply IHΔ; auto.
  }
Qed.

Fixpoint ftf_as_fn_of_vars (f : FTF) (σs : list Entropy) : Entropy :=
  match f with
  | Leaf l => match σs with
              | [σ] => σ
              | _ => dummy_entropy
              end
  | f0 ;; f1 =>
    join
      (ftf_as_fn_of_vars f0 (firstn (length (vars_of f0)) σs))
      (ftf_as_fn_of_vars f1 (skipn (length (vars_of f0)) σs))
  end.

Lemma ftf_as_fn_of_vars_correct f :
  forall σ,
    ftf_as_fn_of_vars f (apply_paths (vars_of f) σ) = apply_FTF f σ.
Proof.
  induction f; intros; auto.
  cbn.
  rewrite apply_paths_app.
  rewrite firstn_app_3; try apply map_length.
  rewrite skipn_app; try apply map_length.
  rewrite <- IHf1, <- IHf2.
  reflexivity.
Qed.

Lemma nondup_good (f : FTF) :
  nondup f -> good f.
Proof.
  intros.
  constructor; auto.
  rewrite nondup_is_vars_nondup in H.

  rewrite pushforward_as_bind.
  rewrite <- meas_id_right.
  extensionality A.
  unfold ">>=".
  cbn.
  unfold dirac.
  set (g := indicator A).
  clearbody g.

  setoid_rewrite <- ftf_as_fn_of_vars_correct.

  pose proof integrate_by_entropies_unfold.
  specialize (H0 (vars_of f)).
  specialize (H0 (g ∘ ftf_as_fn_of_vars f) H).
  setoid_rewrite <- H0.
  clear H0.

  revert g.
  induction f; intros. {
    cbn in *.
    reflexivity.
  } {
    cbn in *.
    unfold compose.
    rewrite app_length.
    rewrite integrate_by_entropies_nest.

    apply paths_nondup_app in H.
    repeat destruct H as [?H0 H].
    spec1 IHf1; auto.
    spec1 IHf2; auto.

    transitivity (
        integrate_by_entropies
          (fun σls =>
             integrate_by_entropies
               (fun σrs =>
                  g (join (ftf_as_fn_of_vars f1 σls)
                          (ftf_as_fn_of_vars f2 σrs)))
               (length (vars_of f2)))
          (length (vars_of f1))).
    {
      apply integrate_by_entropies_n_ext.
      intros.
      apply integrate_by_entropies_n_ext.
      intros.
      rewrite firstn_app_3; auto.
      rewrite skipn_app; auto.
    }

    transitivity (
      integration
        (fun σl =>
           integration
             (fun σr =>
                g (join σl σr))
             μEntropy)
        μEntropy).
    {
      specialize (IHf1 (fun σl =>
                          integrate_by_entropies
                            (fun σrs =>
                               g (join σl (ftf_as_fn_of_vars f2 σrs)))
                            (length (vars_of f2)))).
      setoid_rewrite IHf1.
      clear IHf1.
      integrand_extensionality σl.
      specialize (IHf2 (fun σr => g (join σl σr))).
      setoid_rewrite IHf2.
      reflexivity.
    }
    rewrite <- integration_πL_πR.
    setoid_rewrite join_πL_πR.
    reflexivity.
  }
Qed.

Lemma diagram (Δ Δ' : list path) (f f' : Entropy -> R+) (g : list Entropy -> R+) :
  paths_nondup Δ ->
  paths_nondup Δ' ->
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