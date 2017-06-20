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

Lemma nondup_app (l0 l1 : list path) :
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
  apply nondup_app.
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

Theorem strong_nat_rect (P : nat -> Type) :
  (forall n, (forall m, m < n -> P m) -> P n) ->
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
  induction m using strong_nat_rect.
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

  pose proof splits_nondup H0.
  pose proof @splits_max_len' Δ.

  spec1 H3. {
    destruct Δ as [|[|] Δ]; cbn in *; try tauto.
    destruct (max_list_len Δ); discriminate.
  }

  do 2 (setoid_rewrite <- H; auto).

  unfold compose.
  rewrite <- integration_πL_πR.
  integrand_extensionality σ.

  rewrite reinterleave_splits; auto.
Qed.

Lemma diagram (Δ Δ' : list path) (g : list Entropy -> R+) :
  nondup Δ ->
  nondup Δ' ->
  length Δ = length Δ' ->
  integration (g ∘ apply_paths Δ) μEntropy = integration (g ∘ apply_paths Δ') μEntropy.
Proof.
  intros.
  rewrite 2 integrate_by_entropies_unfold; try assumption.
  rewrite H1.
  reflexivity.
Qed.

Lemma diagram' (Δ Δ' : list path) (f f' : Entropy -> R+) (g : list Entropy -> R+) :
  nondup Δ ->
  nondup Δ' ->
  length Δ = length Δ' ->
  f = g ∘ apply_paths Δ ->
  f' = g ∘ apply_paths Δ' ->
  integration f μEntropy = integration f' μEntropy.
Proof.
  intros.
  subst.
  apply diagram; auto.
Qed.

Inductive FTF :=
| Leaf (l : path)
| Node (tL tR : FTF)
.

Infix ";;" := Node (at level 60, right associativity).

Fixpoint vars_of (f : FTF) : list path :=
  match f with
  | Leaf l => [l]
  | Node tL tR => vars_of tL ++ vars_of tR
  end.

Fixpoint apply_FTF (f : FTF) (σ : Entropy) : Entropy :=
  match f with
  | Leaf l => apply_path l σ
  | fL ;; fR => join (apply_FTF fL σ) (apply_FTF fR σ)
  end.

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

Lemma apply_paths_app l0 l1 σ :
  apply_paths (l0 ++ l1) σ = apply_paths l0 σ ++ apply_paths l1 σ.
Proof.
  apply map_app.
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

Lemma skipn_app {X} n (l0 l1 : list X) :
  length l0 = n ->
  skipn n (l0 ++ l1) = l1.
Proof.
  intros; subst.
  induction l0; auto.
Qed.

Lemma skipn_app_2 {X} n (l0 l1 : list X) :
  n <= length l0 ->
  skipn n (l0 ++ l1) = skipn n l0 ++ l1.
Proof.
  revert l0.
  induction n; cbn; intros; auto. {
    destruct l0; cbn in *; try omega.
    apply IHn.
    omega.
  }
Qed.

Lemma ftf_as_fn_of_vars_correct f :
  apply_FTF f =
  ftf_as_fn_of_vars f ∘ apply_paths (vars_of f).
Proof.
  induction f; intros; auto.
  extensionality σ.
  cbn.
  rewrite apply_paths_app.
  rewrite firstn_app_3; [| apply map_length].
  rewrite skipn_app; [| apply map_length].
  rewrite IHf1, IHf2.
  reflexivity.
Qed.

Definition nondup_ftf (f : FTF) := nondup (vars_of f).
Definition good (f : FTF) := pushforward μEntropy (apply_FTF f) = μEntropy.

Definition comm_FTF : FTF :=
  Leaf [R] ;; Leaf [L].
Definition let_comm_FTF : FTF :=
  Leaf [R; L] ;; Leaf [L] ;; Leaf [R; R].
Definition assoc_l_FTF : FTF :=
  (Leaf [L] ;; Leaf [R; L]) ;; Leaf [R; R].
Definition assoc_r_FTF : FTF :=
  Leaf [L; L] ;; Leaf [L; R] ;; Leaf [R].
Definition πR_FTF : FTF := Leaf [R].

Definition running_examples := [comm_FTF; let_comm_FTF; assoc_l_FTF; assoc_r_FTF; πR_FTF].

Lemma all_nondup : Forall nondup_ftf running_examples.
Proof.
  repeat constructor.
Qed.

Fixpoint covars (f : FTF) : list path :=
  match f with
  | Leaf _ => [[]]
  | fL ;; fR => map (cons L) (covars fL) ++ map (cons R) (covars fR)
  end.

Lemma fold_apply_paths σ :
  map (flip apply_path σ) = (fun ps => apply_paths ps σ).
Proof.
  reflexivity.
Qed.

Lemma apply_paths_map_cons d l σ :
  apply_paths (map (cons d) l) σ = apply_paths l (πd d σ).
Proof.
  apply map_map.
Qed.

Lemma apply_paths_map_snoc d l σ :
  apply_paths (map (fun l' => l' ++ [d]) l) σ = map (πd d) (apply_paths l σ).
Proof.
  setoid_rewrite map_map.
  cbn.
  apply map_ext.
  intros.
  revert σ.
  induction a; cbn; auto.
Qed.

Fixpoint ftf_map (g : path -> path) (f : FTF) : FTF :=
  match f with
  | Leaf p => Leaf (g p)
  | fL ;; fR => ftf_map g fL ;; ftf_map g fR
  end.

Fixpoint id_tree (f : FTF) : FTF :=
  match f with
  | Leaf _ => Leaf []
  | fL ;; fR => ftf_map (cons L) (id_tree fL) ;; ftf_map (cons R) (id_tree fR)
  end.

Lemma apply_of_cons d f σ :
  apply_FTF (ftf_map (cons d) f) σ = apply_FTF f (πd d σ).
Proof.
  revert σ.
  induction f; cbn; intros; auto.
  rewrite IHf1, IHf2; auto.
Qed.

Lemma id_tree_correct f σ :
  apply_FTF (id_tree f) σ = σ.
Proof.
  revert σ.
  induction f; intros; auto.
  cbn in *.
  rewrite 2 apply_of_cons.
  rewrite IHf1, IHf2.
  apply join_πL_πR.
Qed.

Lemma vars_of_nonempty f : vars_of f <> [].
Proof.
  induction f; cbn; try discriminate.
  destruct (vars_of f1), (vars_of f2); discriminate || contradiction.
Qed.

Lemma vars_of_map (f : FTF) g :
  vars_of (ftf_map g f) = map g (vars_of f).
Proof.
  induction f; auto.
  cbn.
  rewrite map_app.
  rewrite IHf1, IHf2.
  auto.
Qed.

Lemma cons_preserves_nondup Δ d :
  nondup Δ <-> nondup (map (cons d) Δ).
Proof.
  induction Δ; cbn; intuition idtac. {
    inject H1.
    constructor; auto.
    rewrite Forall_forall in *.
    intros.
    rewrite in_map_iff in H1.
    inject H1.
    inject H2.
    constructor.
    auto.
  } {
    inject H1.
    constructor; auto.
    rewrite Forall_forall in *.
    intros.
    specialize (H4 (d :: x)).
    spec1 H4; [apply in_map; auto |].
    inject H4.
    auto.
  }
Qed.

Lemma id_tree_nondup f : nondup_ftf (id_tree f).
Proof.
  unfold nondup_ftf.
  induction f; cbn; intros. {
    repeat constructor.
  } {
    apply nondup_app.
    rewrite !vars_of_map.
    rewrite <- !cons_preserves_nondup.
    setoid_rewrite in_map_iff.
    intuition idtac.
    destruct H, H0.
    inject H.
    inject H0.
    constructor.
  }
Qed.

Lemma id_tree_inv {X} f (g : Entropy -> X) :
  g = (g ∘ ftf_as_fn_of_vars (id_tree f)) ∘ apply_paths (vars_of (id_tree f)).
Proof.
  change (g = g ∘ (ftf_as_fn_of_vars (id_tree f) ∘ apply_paths (vars_of (id_tree f)))).
  rewrite <- ftf_as_fn_of_vars_correct.
  extensionality σ.
  cbn.
  rewrite id_tree_correct.
  reflexivity.
Qed.

Lemma id_tree_len f :
  length (vars_of (id_tree f)) = length (vars_of f).
Proof.
  induction f; cbn; auto.
  rewrite !app_length, <- IHf1, <- IHf2.
  rewrite !vars_of_map.
  rewrite !map_length.
  reflexivity.
Qed.

Inductive permutation : nat -> Type :=
| permute_nil : permutation O
| permute_at p {n} : p <= n -> permutation n -> permutation (S n)
.

Fixpoint permute_fn {X n} (p : permutation n) (l : list X) :=
  match p, l with
  | _, [] | permute_nil, _ => []
  | permute_at pos _ p', x :: l' =>
    let l'' := permute_fn p' l' in
    firstn pos l'' ++ [x] ++ skipn pos l''
  end.

Lemma permute_fn_len {X n} (p : permutation n) (l : list X) :
  length (permute_fn p l) = min n (length l).
Proof.
  revert l.
  induction p; cbn in *; intros. {
    destruct l; auto.
  } {
    destruct l0; cbn; auto.
    rewrite app_length.
    cbn.
    rewrite <- plus_n_Sm.
    rewrite <- app_length.
    rewrite firstn_skipn.
    rewrite IHp.
    reflexivity.
  }
Qed.

Lemma permute_fn_len' {X n} (p : permutation n) (l : list X) :
  length l = n ->
  length (permute_fn p l) = n.
Proof.
  intros.
  subst.
  rewrite permute_fn_len.
  apply Min.min_l.
  reflexivity.
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

Lemma integrate_entropies_roll g n :
  integration (fun σ => integrate_by_entropies (fun σs => g (σ :: σs)) n) μEntropy =
  integrate_by_entropies (fun σs => integration (fun σ => g (σs ++ [σ])) μEntropy) n.
Proof.
  revert g.
  induction n; cbn; intros; auto.

  integrand_extensionality σ.
  apply (IHn (g ∘ cons σ)).
Qed.

Lemma tonelli_entropies m n f :
  integrate_by_entropies (fun σn => integrate_by_entropies (fun σm => f σn σm) m) n =
  integrate_by_entropies (fun σm => integrate_by_entropies (fun σn => f σn σm) n) m.
Proof.
  revert f.
  induction m; cbn; intros; auto.
  rewrite tonelli_entropies_and_entropy.
  integrand_extensionality σ.
  apply IHm.
Qed.

Lemma integrate_entropy_app_comm g n m :
  integrate_by_entropies (fun σn => integrate_by_entropies (fun σm => g (σm ++ σn)) m) n =
  integrate_by_entropies (fun σn => integrate_by_entropies (fun σm => g (σn ++ σm)) m) n.
Proof.
  revert g m.
  induction n; intros. {
    cbn.
    setoid_rewrite app_nil_r.
    reflexivity.
  } {
    transitivity (
        integrate_by_entropies
          (fun σn => integrate_by_entropies (fun σm => g (σm ++ σn)) (S m)) n).
    {
      clear.
      cbn.
      rewrite tonelli_entropies_and_entropy.
      setoid_rewrite tonelli_entropies.
      setoid_rewrite app_comm_cons.

      setoid_rewrite (integrate_entropies_roll
                        (fun σs => integrate_by_entropies (fun σn => g (σs ++ σn)) n)).
      setoid_rewrite <- app_assoc.
      cbn.
      rewrite tonelli_entropies_and_entropy.
      reflexivity.
    } {
      cbn.
      rewrite tonelli_entropies_and_entropy.
      integrand_extensionality σ.
      apply (IHn (g ∘ (cons σ))).
    }
  }
Qed.

Lemma integral_permute {n} (p : permutation n) g :
  integrate_by_entropies (g ∘ permute_fn p) n = integrate_by_entropies g n.
Proof.
  revert g.

  induction p; intros. {
    cbn.
    reflexivity.
  } {
    cbn.

    transitivity (
        integrate_by_entropies
          (fun σs =>
             integrate_by_entropies
               (fun σs' => g (σs ++ σs'))
               (S (n - p)))
          p); revgoals.
    {
      setoid_rewrite <- integrate_entropy_app_comm.
      cbn.
      rewrite tonelli_entropies_and_entropy.
      setoid_rewrite (integrate_entropy_app_comm (g ∘ cons _)).
      setoid_rewrite <- integrate_by_entropies_nest.
      integrand_extensionality σ.
      f_equal.
      omega.
    } {
      cbn.
      setoid_rewrite tonelli_entropies_and_entropy.
      integrand_extensionality σ.
      setoid_rewrite (IHp (fun σs => g (firstn p σs ++ [σ] ++ skipn p σs))).
      clear IHp.

      replace n with (p + (n - p)) at 1 by omega.
      rewrite integrate_by_entropies_nest.
      cbn.
      repeat (apply integrate_by_entropies_n_ext; intros).
      repeat f_equal. {
        rewrite firstn_app_3; auto.
      } {
        rewrite skipn_app; auto.
      }
    }
  }
Qed.

Lemma compose_assoc {A B C D} (f : A -> B) (g : B -> C) (h : C -> D) :
  h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof.
  reflexivity.
Qed.

Fixpoint permute_app {n0 n1} (p0 : permutation n0) (p1 : permutation n1) : permutation (n0 + n1) :=
  match p0 in permutation n0' return permutation (n0' + n1) with
  | permute_nil => p1
  | permute_at pos Hpos p0' =>
    permute_at pos (le_trans _ _ _ Hpos (Nat.le_add_r _ _))
               (permute_app p0' p1)
  end.

Lemma permute_app_correct {X n0 n1} p0 p1 :
  forall (l0 l1 : list X),
    length l0 = n0 ->
    length l1 = n1 ->
    permute_fn (@permute_app n0 n1 p0 p1) (l0 ++ l1) = permute_fn p0 l0 ++ permute_fn p1 l1.
Proof.
  intros.
  revert l0 H.
  induction p0; cbn; intros. {
    destruct l0; try discriminate.
    reflexivity.
  } {
    destruct l0; try discriminate.
    cbn.
    inject H.
    specialize (IHp0 _ eq_refl).
    rewrite IHp0.
    rewrite firstn_app.
    rewrite permute_fn_len'; auto.
    replace (p - length l0) with O by omega.
    cbn.
    rewrite app_nil_r.
    rewrite <- app_assoc.
    cbn.
    rewrite skipn_app_2; auto.
    rewrite permute_fn_len'; auto.
  }
Qed.

Lemma nondup_good f : nondup_ftf f -> good f.
Proof.
  intros.
  hnf.
  rewrite <- meas_id_right.
  rewrite pushforward_as_bind.
  extensionality A.
  unfold dirac, ">>=".
  cbn.
  set (g := indicator A).
  clearbody g.
  clear A.

  change (integration (g ∘ apply_FTF f) μEntropy = integration g μEntropy).
  rewrite ftf_as_fn_of_vars_correct.
  rewrite compose_assoc.
  rewrite integrate_by_entropies_unfold; auto.

  revert g.
  induction f; cbn; intros. {
    reflexivity.
  } {
    unfold compose.
    rewrite app_length.
    rewrite integrate_by_entropies_nest.

    transitivity (
        integrate_by_entropies
          (fun σsL =>
             integrate_by_entropies
               (fun σsR =>
                  g
                    (join (ftf_as_fn_of_vars f1 σsL)
                          (ftf_as_fn_of_vars f2 σsR)))
               (length (vars_of f2)))
          (length (vars_of f1))).
    {
      apply integrate_by_entropies_n_ext; intros.
      apply integrate_by_entropies_n_ext; intros.
      rewrite firstn_app_3; auto.
      rewrite skipn_app; auto.
    }

    unfold nondup_ftf in H.
    cbn in H.
    apply nondup_app in H.
    intuition idtac.

    setoid_rewrite (H3 (fun σR => g (join _ σR))).
    setoid_rewrite (H1 (fun σL => integration (fun σR => g (join σL σR)) _)).
    rewrite <- integration_πL_πR.
    setoid_rewrite join_πL_πR.
    reflexivity.
  }
Qed.
