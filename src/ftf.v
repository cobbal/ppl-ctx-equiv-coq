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
Definition πd_n (d : dir) := if d then πL_n else πR_n.

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
Fixpoint path_conflict (p0 p1 : path) : bool :=
  match p0, p1 with
  | [], _ | _, [] => true
  | L :: _, R :: _ => false
  | R :: _, L :: _ => false
  | _ :: p0', _ :: p1' => path_conflict p0' p1'
  end.

Inductive FTF :=
| Leaf (l : path)
| Node (tL tR : FTF)
.

Infix ";;" := Node (at level 60, right associativity).
Print Grammar constr.

Fixpoint conflicts_in (p : path) (f : FTF) : bool :=
  match f with
  | Leaf l => path_conflict p l
  | Node tL tR => conflicts_in p tL || conflicts_in p tR
  end.

Fixpoint vars_of (f : FTF) : list path :=
  match f with
  | Leaf l => [l]
  | Node tL tR => vars_of tL ++ vars_of tR
  end.

Lemma vars_of_conflict f l :
  In l (vars_of f) -> conflicts_in l f = true.
Proof.
  induction f; cbn; intros. {
    inject H; try tauto.
    induction l; auto.
    destruct a; auto.
  } {
    apply in_app_or in H.
    inject H. {
      rewrite IHf1; auto.
    } {
      rewrite IHf2; auto.
      destruct conflicts_in; auto.
    }
  }
Qed.

Inductive nondup : FTF -> Prop :=
| nondup_leaf l : nondup (Leaf l)
| nondup_node tL tR :
    nondup tL ->
    nondup tR ->
    (forall pL pR, In pL (vars_of tL) -> In pR (vars_of tR) -> path_conflict pL pR = false) ->
    nondup (tL ;; tR).

Definition forallb {A} (P : A -> bool) (l : list A) : bool :=
  fold_right andb true (map P l).

Lemma forallb_in {A} (P : A -> bool) (l : list A) (x : A) :
  forallb P l = true ->
  In x l ->
  P x = true.
Proof.
  intros.
  induction l; cbn in *. {
    inject H0.
  } {
    apply andb_prop in H; auto.
    inject H.
    inject H0; subst; auto.
  }
Qed.

Lemma forallb_app {A} (P : A -> bool) (l0 l1 : list A) :
  forallb P (l0 ++ l1) = (forallb P l0 && forallb P l1)%bool.
Proof.
  induction l0; cbn; auto.
  destruct P; auto.
Qed.

Fixpoint compute_nondup (f : FTF) : bool :=
  match f with
  | Leaf l => true
  | Node tL tR =>
    (compute_nondup tL)
      && (compute_nondup tR)
      && (forallb (fun p => negb (conflicts_in p tL)) (vars_of tR))
      && (forallb (fun p => negb (conflicts_in p tR)) (vars_of tL))
  end.

Lemma path_conflict_sym l0 l1 :
  path_conflict l0 l1 = path_conflict l1 l0.
Proof.
  revert l1.
  induction l0; intros. {
    induction l1; auto.
    cbn.
    destruct a; auto.
  } {
    destruct a. {
      induction l1; cbn; auto.
      destruct a; auto.
    } {
      induction l1; cbn; auto.
      destruct a; auto.
    }
  }
Qed.

Lemma path_conflict_refl l :
  path_conflict l l = true.
Proof.
  induction l as [|[|] ?]; cbn; auto.
Qed.

Lemma conflicts_in_reflected_by_path_conflict f p l :
  In p (vars_of f) ->
  path_conflict l p = true ->
  conflicts_in l f = true.
Proof.
  reverse.
  induction f; intros. {
    inject H; tauto.
  } {
    cbn in *.
    apply Bool.orb_true_intro.
    apply in_app_or in H.
    inject H; eauto.
  }
Qed.

Lemma compute_nondup_reflects f :
  compute_nondup f = true <-> nondup f.
Proof.
  induction f; cbn; split; intros; try solve [constructor]. {
    repeat (apply andb_prop in H; destruct H).
    pose proof (proj1 IHf1 H).
    pose proof (proj1 IHf2 H2).
    clear IHf1 IHf2.

    constructor; auto.
    intros.
    eapply forallb_in in H0; eauto.
    eapply forallb_in in H1; eauto.

    pose proof conflicts_in_reflected_by_path_conflict _ _ pL H6.
    destruct (path_conflict pL pR); auto.
    rewrite H7 in *; auto.
  } {
    inject H.

    enough (forall f2 f1,
               (forall pL pR : path,
                   In pL (vars_of f1) ->
                   In pR (vars_of f2) ->
                   path_conflict pL pR = false) ->
               forallb (fun p : path => negb (conflicts_in p f1)) (vars_of f2) = true).
    {
      repeat (apply andb_true_intro; split); try tauto. {
        apply H.
        intros.
        apply H4; auto.
      } {
        apply H.
        intros.
        rewrite path_conflict_sym.
        apply H4; auto.
      }
    }

    clear.
    induction f2; intros. {
      apply andb_true_intro; split; auto.

      specialize (fun pL HL => H pL l HL ltac:(cbn; auto)).

      induction f1. {
        cbn.
        rewrite path_conflict_sym.
        rewrite H; cbn; auto.
      } {
        cbn.
        rewrite Bool.negb_orb.
        rewrite IHf1_1; revgoals. {
          intros.
          apply H.
          cbn.
          apply in_or_app.
          auto.
        }
        rewrite IHf1_2; revgoals. {
          intros.
          apply H.
          cbn.
          apply in_or_app.
          auto.
        }
        trivial.
      }
    } {
      cbn [vars_of] in *.
      rewrite forallb_app.
      rewrite IHf2_1; revgoals. {
        intros.
        apply H; auto.
        apply in_or_app; auto.
      }
      rewrite IHf2_2; revgoals. {
        intros.
        apply H; auto.
        apply in_or_app; auto.
      }
      trivial.
    }
  }
Qed.

Fixpoint apply_path (p : path) : Entropy -> Entropy :=
  match p with
  | [] => id
  | d :: p' => apply_path p' ∘ πd d
  end.

Lemma apply_path_snoc p d σ :
  apply_path (p ++ [d]) σ = πd d (apply_path p σ).
Proof.
  revert σ.
  induction p; intros; auto.
  cbn.
  rewrite IHp.
  reflexivity.
Qed.

Fixpoint apply_FTF (f : FTF) (σ : Entropy) : Entropy :=
  match f with
  | Leaf l => apply_path l σ
  | fL ;; fR => join (apply_FTF fL σ) (apply_FTF fR σ)
  end.

Fixpoint apply_path_n (p : path) : nat -> nat :=
  match p with
  | [] => id
  | d :: p' => πd_n d ∘ apply_path_n p'
  end.

Fixpoint apply_FTF_n (f : FTF) : nat -> nat :=
  match f with
  | Leaf l => apply_path_n l
  | fL ;; fR => fun n => join' (apply_FTF_n fL) (apply_FTF_n fR) n
  end.

Lemma apply_paths_aggree p σ :
  apply_path p σ = σ ∘ apply_path_n p.
Proof.
  extensionality n.
  revert σ n.
  induction p; intros; auto.
  cbn.
  destruct a; unfold compose; rewrite IHp; reflexivity.
Qed.

Lemma apply_FTFs_aggree f σ :
  apply_FTF f σ = σ ∘ apply_FTF_n f.
Proof.
  extensionality n.
  revert σ n.
  induction f; intros. {
    cbn.
    rewrite apply_paths_aggree.
    reflexivity.
  } {
    cbn.
    unfold join.
    unfold join'.
    rewrite IHf1.
    rewrite IHf2.
    cbn.
    destruct PeanoNat.Nat.even; reflexivity.
  }
Qed.

Lemma path_good (p : path) :
  pushforward μEntropy (apply_path p) = μEntropy.
Proof.
  induction p as [|[|]]. {
    reflexivity.
  } {
    cbn.
    rewrite pushforward_as_bind.
    change (μEntropy >>= (fun σ => (fun σL _ => dirac (apply_path p σL)) (πL σ) (πR σ)) = μEntropy).
    rewrite bind_πL_πR.
    extensionality A.
    unfold ">>=".
    rewrite tonelli_sigma_finite; auto.
    erewrite int_const_entropy; eauto.
    intros.
    rewrite pushforward_as_bind in IHp.
    rewrite <- IHp at 2.
    reflexivity.
  } {
    cbn.
    rewrite pushforward_as_bind.
    change (μEntropy >>= (fun σ => (fun _ σR => dirac (apply_path p σR)) (πL σ) (πR σ)) = μEntropy).
    rewrite bind_πL_πR.
    extensionality A.
    unfold ">>=".
    erewrite int_const_entropy; eauto.
    intros.
    rewrite pushforward_as_bind in IHp.
    rewrite <- IHp at 2.
    reflexivity.
  }
Qed.

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
  intros;
  try apply compute_nondup_reflects;
  cbn in *;
  intuition subst;
  reflexivity.


Fixpoint max_var_len (f : FTF) : nat :=
  match f with
  | Leaf l => length l
  | fL ;; fR => max (max_var_len fL) (max_var_len fR)
  end.

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

Fixpoint prepend_to_all_paths (p : path) (f : FTF) : FTF :=
  match f with
  | Leaf l => Leaf (p ++ l)
  | Node tL tR => Node (prepend_to_all_paths p tL) (prepend_to_all_paths p tR)
  end.

Fixpoint append_to_all_paths (p : path) (f : FTF) : FTF :=
  match f with
  | Leaf l => Leaf (l ++ p)
  | Node tL tR => Node (append_to_all_paths p tL) (append_to_all_paths p tR)
  end.

(* Yeah... not much idea what this is doing... *)
Fixpoint ftf_compose (f0 f1 : FTF) {struct f1} : FTF :=
  match f1 with
  | Leaf l => prepend_to_all_paths l f0
  | f1L ;; f1R =>
    (fix rec_f0 f0 :=
       match f0 with
       | Leaf nil => f1
       | Leaf (L :: l') => ftf_compose (Leaf l') f1L
       | Leaf (R :: l') => ftf_compose (Leaf l') f1R
       | f0R ;; f1R => rec_f0 f0R ;; rec_f0 f1R
       end) f0
  end.

Lemma ftf_compose_correct f0 f1 σ :
  apply_FTF (ftf_compose f0 f1) σ = apply_FTF f0 (apply_FTF f1 σ).
Proof.
  revert σ.
  revert f0.
  induction f1; intros. {
    induction f0. {
      cbn.
      revert σ.
      induction l; intros; auto.
      destruct a; cbn; auto.
    } {
      cbn.
      f_equal; auto.
    }
  } {
    induction f0. {
      destruct l as [|[|]]; cbn in *; auto. {
        rewrite πL_join.
        apply IHf1_1.
      } {
        rewrite πR_join.
        apply IHf1_2.
      }
    } {
      cbn in *.
      rewrite IHf0_1, IHf0_2.
      reflexivity.
    }
  }
Qed.

Lemma vars_of_prepend l f :
  vars_of (prepend_to_all_paths l f) =
  map (app l) (vars_of f).
Proof.
  induction f; auto.
  cbn.
  rewrite map_app.
  rewrite IHf1, IHf2.
  reflexivity.
Qed.

Lemma conflicts_in_preprend l p f :
  conflicts_in (l ++ p) (prepend_to_all_paths l f) = conflicts_in p f.
Proof.
  induction f. {
    cbn.
    induction l; auto.
    destruct a; auto.
  } {
    cbn.
    rewrite IHf1, IHf2.
    reflexivity.
  }
Qed.

Lemma forallb_map {A B} P (f : A -> B) l :
  forallb P (map f l) =
  forallb (P ∘ f) l.
Proof.
  induction l; auto.
  cbn.
  setoid_rewrite IHl.
  reflexivity.
Qed.

Lemma forallb_Forall {X} P (l : list X) :
  Forall (fun x => P x = true) l <-> forallb P l = true.
Proof.
  split; intros; induction l; auto. {
    cbn.
    inject H.
    rewrite H2.
    apply IHl.
    auto.
  } {
    cbn in H.
    apply andb_prop in H.
    inject H.
    constructor; eauto.
  }
Qed.

Lemma forall_forallb {X} P (l : list X) :
  (forall x, In x l -> P x = true) <->
  forallb P l = true.
Proof.
  rewrite <- forallb_Forall.
  rewrite <- Forall_forall.
  reflexivity.
Qed.

Lemma prefix_conflict l pL pR :
  path_conflict (l ++ pL) (l ++ pR) = path_conflict pL pR.
Proof.
  induction l; auto.
  destruct a; auto.
Qed.

Lemma compose_good (f0 f1 : FTF) :
  good f0 ->
  good f1 ->
  good (ftf_compose f0 f1).
Proof.
  split. {
    destruct H0 as [H1 _], H as [H0 _].
    (* apply compute_nondup_reflects. *)
    (* apply compute_nondup_reflects in H0. *)
    (* apply compute_nondup_reflects in H1. *)
    revert f0 H0.
    induction f1. {
      intros.
      cbn in *.
      clear H1.
      induction f0; try solve [constructor].
      inject H0.
      constructor; auto.
      fold prepend_to_all_paths.
      rewrite 2 vars_of_prepend.
      setoid_rewrite in_map_iff.
      intros ? ? [pL' [? ?]] [pR' [? ?]].
      subst.
      rewrite prefix_conflict.
      apply H4; auto.
    } {
      intros.
      inject H1.
      intuition idtac.
      induction f0. {
        destruct l as [|[|]]; try apply H; try apply H1; constructor; auto.
      } {
        inject H0.
        intuition idtac.
        change (nondup (ftf_compose f0_1 (f1_1 ;; f1_2) ;; ftf_compose f0_2 (f1_1 ;; f1_2))).
        constructor; eauto 1.
        intros.
        admit.
      }
    }
  } {
    destruct H0 as [_ H1], H as [_ H0].
    setoid_rewrite <- H0 at 2.
    setoid_rewrite <- H1 at 2.
    repeat rewrite pushforward_as_bind.
    rewrite meas_bind_assoc.
    cbn.
    setoid_rewrite meas_id_left.
    cbn.
    unfold compose.
    setoid_rewrite ftf_compose_correct.
    reflexivity.
  }
Abort.

Lemma vars_of_inhabited f :
  vars_of f <> nil.
Proof.
  induction f; try discriminate.
  cbn.
  intro.
  apply app_eq_nil in H.
  tauto.
Qed.

Fixpoint subentropies_by_tree (f : FTF) (σ : Entropy) : list Entropy :=
  match f with
  | Leaf l => [apply_path l σ]
  | fL ;; fR => subentropies_by_tree fL σ ++ subentropies_by_tree fR σ
  end.

Definition subentropies_by_paths (ps : list path) (σ : Entropy) : list Entropy :=
  map (fun p => apply_path p σ) ps.

Lemma subentropies_aggree f :
  subentropies_by_tree f = subentropies_by_paths (vars_of f).
Proof.
  induction f; auto.
  cbn.
  rewrite IHf1, IHf2.
  unfold subentropies_by_paths.
  setoid_rewrite map_app.
  reflexivity.
Qed.

Fixpoint paths_nondup (ps : list path) : bool :=
  match ps with
  | nil => true
  | p :: ps' => forallb (fun p' => negb (path_conflict p p')) ps' && paths_nondup ps'
  end.

Lemma paths_nondup_app (l0 l1 : list path) :
  (paths_nondup l0 = true /\
   paths_nondup l1 = true /\
   (forall p0 p1, In p0 l0 -> In p1 l1 -> path_conflict p0 p1 = false)) <->
  paths_nondup (l0 ++ l1) = true.
Proof.
  intros.
  induction l0. {
    intuition idtac.
    inject H0.
  } {
    split; intros. {
      destruct IHl0 as [? _].
      intuition idtac.
      cbn in H1.
      apply andb_prop in H1.
      intuition idtac.

      cbn.
      apply andb_true_intro.
      split. {
        apply forall_forallb.
        intros.
        apply in_app_or in H2.
        rewrite <- forall_forallb in H0.
        inject H2; auto.
        rewrite H3; auto.
        left; auto.
      } {
        apply H1.
        intros.
        apply H3; auto.
        right; auto.
      }
    } {
      destruct IHl0 as [_ ?].
      cbn in H.
      apply andb_prop in H.
      rewrite <- forall_forallb in H.
      intuition idtac. {
        cbn.
        apply andb_true_intro; split; auto.
        rewrite <- forall_forallb.
        intros.
        apply H1.
        apply in_or_app; auto.
      } {
        inject H3. {
          specialize (H1 p1).
          destruct path_conflict; auto.
          discriminate H1.
          apply in_or_app; auto.
        } {
          apply H4; auto.
        }
      }
    }
  }
Qed.

Lemma nondup_is_vars_nondup (f : FTF) :
  compute_nondup f = paths_nondup (vars_of f).
Proof.
  enough (nondup f <-> paths_nondup (vars_of f) = true). {
    rewrite <- compute_nondup_reflects in H.
    inject H.
    destruct compute_nondup, paths_nondup; auto.
    discriminate H0.
    reflexivity.
  }

  induction f. {
    split; constructor.
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

Lemma apply_paths_app l0 l1 σ :
  apply_paths (l0 ++ l1) σ = apply_paths l0 σ ++ apply_paths l1 σ.
Proof.
  apply map_app.
Qed.

Definition apply_paths_n (ps : list path) (n : nat) : list nat :=
  map (fun p => apply_path_n p n) ps.

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

Inductive permutation_of {X} : list X -> list X -> Prop :=
| perm_nil : permutation_of [] []
| perm_cons x l0 l1 l1' :
    permutation_of l0 (l1 ++ l1') ->
    permutation_of (x :: l0) (l1 ++ x :: l1')
.

Lemma perm_refl {X} (l : list X) : permutation_of l l.
Proof.
  induction l; try constructor.
  change (permutation_of ([] ++ a :: l) ([] ++ a :: l)).
  constructor.
  auto.
Qed.

Lemma split_nondups Δ σ :
  (~ In [] Δ) ->
  permutation_of
    (apply_paths Δ σ)
    (apply_paths (splits_left Δ) (πL σ) ++ apply_paths (splits_right Δ) (πR σ)).
Proof.
  intros.
  cbn in H.
  revert σ.
  induction Δ; auto; intros. {
    apply perm_refl.
  }
  cbn in *.
  (* apply andb_prop in H0. *)
  (* rewrite <- forall_forallb in H0. *)
  rewrite 2 map_app.
  intuition idtac.

  fold (apply_paths Δ σ).
  fold (apply_paths (splits_left Δ) (πL σ)).
  fold (apply_paths (splits_right Δ) (πR σ)).

  destruct a as [|[|] p]; try tauto; clear H0. {
    cbn.
    refine (perm_cons _ _ [] _ _).
    apply H.
  } {
    cbn.
    constructor.
    apply H.
  }
Qed.

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

Lemma snoc_len {X n l} (x : X) :
  length l = n ->
  length (l ++ [x]) = S n.
Proof.
  intros.
  subst.
  rewrite app_length.
  cbn.
  omega.
Qed.

Definition nvl n := list {p : path | length p = n}.

Definition nvl_list {n} : nvl n -> list path := map (@proj1_sig _ _).

Lemma nvl_list_app {n} (nl nl' : nvl n) :
  nvl_list (nl ++ nl') = nvl_list nl ++ nvl_list nl'.
Proof.
  apply map_app.
Qed.

Definition dep_snoc {n} d (p : {p : path | length p = n}) : {p : path | length p = S n} :=
  let (p, Hp) := p in
  exist _ (p ++ [d]) (snoc_len _ Hp).

Definition dep_cons {n} d (p : {p : path | length p = n}) : {p : path | length p = S n} :=
  let (p, Hp) := p in
  exist _ (d :: p) (eq_S _ _ Hp).

Fixpoint build_tree n : nvl n :=
  match n with
  | O => [exist _ [] eq_refl]
  | S n' => map (dep_cons L) (build_tree n') ++ map (dep_cons R) (build_tree n')
  end.

Fixpoint pad_variable n (p : path) : nvl n :=
  match p, n with
  | [], _ => build_tree n
  | _, O => (* garbage *) []
  | d :: p', S n' => map (dep_cons d) (pad_variable n' p')
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
  rewrite IHn.
  omega.
Qed.

Lemma pad_variable_len n p :
  length p <= n ->
  length (pad_variable n p) = (2 ^ (n - length p)).
Proof.
  revert n.
  induction p; intros. {
    destruct n; auto.
    cbn -[build_tree].
    rewrite len_build_tree.
    reflexivity.
  } {
    cbn in *.
    destruct n; try omega.
    specialize (IHp n ltac:(omega)).
    cbn.
    rewrite map_length.
    auto.
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
    contradict H0.
    apply Nat.nlt_0_r.
  } {
    apply H.
    intros.
    apply IHn.
    abstract omega.
  }
Defined.

Lemma skipn_length {X} n (l : list X) :
  length (skipn n l) = length l - n.
Proof.
  revert l.
  induction n; destruct l; cbn; auto.
Qed.

Lemma proj1_dep_cons d n l :
  proj1_sig (@dep_cons n d l) = d :: proj1_sig l.
Proof.
  destruct l; auto.
Qed.

Lemma nvl_list_map_dep_cons d n (l : nvl n) :
  nvl_list (map (dep_cons d) l) =
  map (cons d) (nvl_list l).
Proof.
  intros.
  induction l; cbn; auto.
  destruct a; cbn.
  f_equal.
  auto.
Qed.

Lemma apply_dep_cons d n (l : nvl n) σ :
  apply_paths (nvl_list (map (dep_cons d) l)) σ =
  apply_paths (nvl_list l) (πd d σ).
Proof.
  induction l; cbn; auto.
  destruct a; cbn; auto.
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
  apply_paths (nvl_list (build_tree n)) (join_the_build n l) = l.
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

    rewrite nvl_list_app.
    rewrite 2 nvl_list_map_dep_cons.
    setoid_rewrite map_app.
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

Definition normalize (Δ : list path) n : nvl n := flat_map (pad_variable n) Δ.

Fixpoint normalized_lookups (Δ : list path) n (l : list Entropy) : list Entropy :=
  match Δ with
  | [] => l
  | p :: Δ' =>
    (join_the_build (n - length p) (firstn (length (pad_variable n p)) l))
      :: normalized_lookups Δ' n (skipn (length (pad_variable n p)) l)
  end.

Lemma apply_build_tree_injective n :
  Injective (apply_paths (nvl_list (build_tree n))).
Proof.
  hnf.
  induction n; intros. {
    inject H.
    auto.
  } {
    cbn -[apply_paths] in H.
    rewrite !nvl_list_app, !apply_paths_app, !apply_dep_cons in H.
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
    join_the_build (n - length p) (apply_paths (nvl_list (pad_variable n p)) σ) =
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
    normalized_lookups Δ n (apply_paths (nvl_list (normalize Δ n)) σ) =
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
    rewrite nvl_list_app.

    rewrite apply_paths_app.

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

Fixpoint zipwith {X Y Z} (f : X -> Y -> Z) (xs : list X) (ys : list Y) : list Z :=
  match xs, ys with
  | [], _ | _, [] => []
  | x :: xs', y :: ys' => f x y :: zipwith f xs' ys'
  end.

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

Lemma split_integrate_by_entropies g n :
  integrate_by_entropies g n =
  integrate_by_entropies
    (fun σls => integrate_by_entropies (fun σrs => g (zipwith join σls σrs)) n) n.
Proof.
  revert g.
  induction n; intros; auto.
  cbn.
  setoid_rewrite tonelli_entropies_and_entropy.
  setoid_rewrite <- integration_πL_πR.
  setoid_rewrite join_πL_πR.
  integrand_extensionality σ.
  apply IHn.
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
  paths_nondup Δ = true ->
  paths_nondup (splits_left Δ) = true.
Proof.
  induction Δ; intros; auto.
  replace (a :: Δ) with ([a] ++ Δ) in * by auto.
  apply paths_nondup_app in H.
  cbn.
  apply paths_nondup_app.
  intuition idtac. {
    destruct a as [|[|]]; auto.
  } {
    apply in_split_left in H3.
    apply in_splits_left in H4.
    subst.
    specialize (H2 (L :: p0) (L :: p1) ltac:(cbn; auto) H4).
    cbn in H2.
    assumption.
  }
Qed.

Lemma splits_right_nondup {Δ} :
  paths_nondup Δ = true ->
  paths_nondup (splits_right Δ) = true.
Proof.
  induction Δ; intros; auto.
  replace (a :: Δ) with ([a] ++ Δ) in * by auto.
  apply paths_nondup_app in H.
  cbn.
  apply paths_nondup_app.
  intuition idtac. {
    destruct a as [|[|]]; auto.
  } {
    apply in_split_right in H3.
    apply in_splits_right in H4.
    subst.
    specialize (H2 (R :: p0) (R :: p1) ltac:(cbn; auto) H4).
    cbn in H2.
    assumption.
  }
Qed.

Lemma length_of_splits Δ :
  ~ In [] Δ ->
  length Δ = length (splits_left Δ) + length (splits_right Δ).
Proof.
  induction Δ; intros; auto.

  spec1 IHΔ; cbn in *; try tauto.
  destruct a as [|[|]]; cbn in *; try tauto; omega.
Qed.

Lemma nil_in_nondup Δ :
  paths_nondup Δ = true ->
  In [] Δ ->
  Δ = [[]].
Proof.
  intros.
  destruct Δ; try tauto.
  destruct p. {
    destruct Δ; auto.
    cbn in *.
    discriminate.
  }
  exfalso.
  apply andb_prop in H.
  destruct H as [H _].
  inject H0; try discriminate.
  eapply forall_forallb in H; eauto.
  cbn in H.
  destruct d; discriminate.
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
  paths_nondup Δ = true ->
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
        solve [discriminate | omega].
    } {
      destruct p; cbn in *; try omega.
      reflexivity.
    }
  } {
    (* rewrite split_integrate_by_entropies. *)

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
        setoid_rewrite map_length.
        rewrite app_length, !map_length, !len_build_tree.
        reflexivity.
      }
      setoid_rewrite H.
      clear H.

      rewrite skipn_all2; auto.
      repeat setoid_rewrite map_length.
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

Lemma max_var_len_as_list f :
  max_var_len f = max_list_len (vars_of f).
Proof.
  induction f. {
    cbn.
    symmetry.
    apply max_l.
    omega.
  } {
    cbn.
    rewrite IHf1, IHf2.
    setoid_rewrite max_list_len_app.
    reflexivity.
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
  rewrite map_app.
  rewrite firstn_app_3; try apply map_length.
  rewrite skipn_app; try apply map_length.
  rewrite <- IHf1, <- IHf2.
  reflexivity.
Qed.

Lemma integral_of_apply_FTF f g :
  integration (fun σ => g (apply_FTF f σ)) μEntropy =
  integrate_by_entropies (fun σs => g (join_the_build (max_var_len f) σs)) (2 ^ max_var_len f).
Proof.
  remember (max_var_len f).
  rewrite max_var_len_as_list in Heqn.
Abort.

Lemma nondup_good (f : FTF) :
  nondup f -> good f.
Proof.
  intros.
  constructor; auto.
  apply compute_nondup_reflects in H.
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
