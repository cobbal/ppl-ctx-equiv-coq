Require Import Reals.
Require Import List.
Require Import Ensembles.
Require Import Coq.Logic.JMeq.
Require Import utils.
Require Import syntax.
Require Import RelationClasses.

Local Open Scope ennr.

Section AbstractMachine.
  (* τP is the type of the whole program *)
  Variables τP : Ty.
  Definition result := option (val τP ⨉ R+).

  Inductive kont : Ty -> Type :=
  | kHalt : kont τP

  | kAppFn {τa τr} (σ : Entropy) (ea : expr · τa) (k : kont τr)
    : kont (τa ~> τr)
  | kAppArg {τa τr} (σ : Entropy) (vf : val (τa ~> τr)) (k : kont τr)
    : kont τa

  | kFactor (k : kont ℝ)
    : kont ℝ

  | kPlusL (σ : Entropy) (er : expr · ℝ) (k : kont ℝ)
    : kont ℝ
  | kPlusR (vl : val ℝ) (k : kont ℝ)
    : kont ℝ
  .

  Inductive state τ :=
  | mk_state (c : expr · τ) (σ : Entropy) (w : R+) (k : kont τ)
  .
  Arguments mk_state {τ} c σ w k.

  Definition exstate := {τ : Ty & state τ}.
  Definition mk_exstate {τ} c σ w k :=
    existT _ τ (mk_state c σ w k).

  (* Lemma dummy_entropy : Entropy. *)
  (* Proof. *)
  (*   exists 0%R. *)
  (*   split. { *)
  (*     apply Rle_refl. *)
  (*   } { *)
  (*     apply Rlt_le. *)
  (*     apply Rlt_0_1. *)
  (*   } *)
  (* Qed. *)

  Lemma discriminate_option {A} {x : A} : (~ None = Some x).
  Proof.
    discriminate.
  Qed.

  Reserved Infix "-->" (at level 84).
  Inductive step : forall {τ τ'}, state τ -> state τ' -> Type :=
  (* not a value, destruct the expression *)
  | step_app : forall {τa τr ef ea σ w k},
      @mk_state τr (e_app ef ea) σ w k -->
      @mk_state (τa ~> τr) ef (πL σ) w (kAppFn (πR σ) ea k)
  | step_factor : forall {e σ w k},
      @mk_state ℝ (e_factor e) σ w k -->
      @mk_state ℝ e σ w (kFactor k)
  | step_sample : forall {σ w k},
      @mk_state ℝ e_sample σ w k -->
      @mk_state ℝ (v_real (proj1_sig (σ O))) σ w k
  | step_plus : forall {el er σ w k},
      @mk_state ℝ (e_plus el er) σ w k -->
      @mk_state ℝ el (πL σ) w (kPlusL (πR σ) er k)

  (* is a value, destruct the continuation *)
  | step_k_app_fn : forall {τa τr} {vf : val (τa ~> τr)} {ea σ_unused σ w k},
      @mk_state (τa ~> τr) vf σ_unused w (kAppFn σ ea k) -->
      @mk_state τa ea (πL σ) w (kAppArg (πR σ) vf k)
  | step_k_app_arg : forall {τa τr} {va : val τa} {body σ_unused σ w k},
      @mk_state τa va σ_unused w (kAppArg σ (v_lam body) k) -->
      @mk_state τr (proj1_sig (ty_subst1 body va)) (πL σ) w k
  | step_k_factor : forall {r σ_unused w k} (rpos : (0 <= r)%R),
      @mk_state ℝ (e_real r) σ_unused w (kFactor k) -->
      @mk_state ℝ (e_real r) σ_unused (w * finite r rpos) k
  | step_k_plus_l : forall {vl : val ℝ} {er σ_unused σ w k},
      @mk_state ℝ vl σ_unused w (kPlusL σ er k) -->
      @mk_state ℝ er (πL σ) w (kPlusR vl k)
  | step_k_plus_r : forall {rl rr : R} {σ w k},
      @mk_state ℝ (e_real rr) σ w (kPlusR (v_real rl) k) -->
      @mk_state ℝ (e_real (rl + rr)%R) σ w k
  where "s0 --> s1" := (step s0 s1).

  Lemma decide_val {τ} (e : expr · τ) :
    {is_val e} + {~ is_val e}.
  Proof.
    destruct e; cbn; solve [left; auto | right; auto].
  Qed.

  Lemma step_deterministic τ (s : state τ) :
    {s' : exstate &
      (s --> projT2 s') ⨉
      forall s'', (s --> projT2 s'') -> s' = s''
    } +
    ({s' : exstate & s --> projT2 s'} -> False).
  Proof.
    destruct s.
    destruct (decide_val c). {
      (* pose (mk_val c i). *)
      (* replace c with (v : expr · τ) by auto. *)
      (* clearbody v. *)
      (* clear i c. *)

      destruct k. {
        right.
        intros [[τ' s'] H].
        inversion H; subst*. {
          d_destruct H3.
          contradiction i.
        } {
          revert H4 i; clear; intros.
          d_destruct H4.
          contradiction i.
        } {
          revert H4 i; clear; intros.
          d_destruct H4.
          contradiction i.
        } {
          revert H4 i; clear; intros.
          d_destruct H4.
          contradiction i.
        }
      } {
        left.
        pose (mk_val c i).
        replace c with (v : expr · _) in * by auto.
        clearbody v.
        clear c i.

        destruct_val v.

        eexists (mk_exstate _ _ _ _); repeat constructor.
        intros [τ' s''] H.
        cbn in *.
        d_destruct H.
        destruct_val vf.
        d_destruct x.
        auto.
      } {
        left.
        pose (mk_val c i).
        replace c with (v : expr · _) in * by auto.
        clearbody v.
        clear c i.

        destruct_val vf.

        eexists (mk_exstate _ _ _ _); repeat constructor.
        intros [τ' s''] H.
        cbn in *.
        d_destruct H; try absurd_val.

        rewrite (val_eq x).
        auto.
      } {
        pose (mk_val c i).
        replace c with (v : expr · _) in * by auto.
        clearbody v.
        clear c i.

        destruct_val v.
        destruct (Rle_dec 0 r). {
          left.

          eexists (mk_exstate _ _ _ _); repeat constructor.
          intros [τ' s''] H.
          cbn in *.
          d_destruct H.

          unfold mk_exstate.
          do 3 f_equal.

          apply finite_inj with (r0_pos := r0).
          auto.
        } {
          right.

          intros [[τ' s'] H].
          cbn in *.

          inversion H; subst.
          contradiction.
        }
      } {
        left.
        pose (mk_val c i).
        replace c with (v : expr · _) in * by auto.
        clearbody v.
        clear c i.

        eexists (mk_exstate _ _ _ _); repeat constructor.
        intros [τ' s''] H.
        cbn in *.

        d_destruct H; try absurd_val.

        rewrite (val_eq x).
        auto.
      } {
        left.
        pose (mk_val c i).
        replace c with (v : expr · _) in * by auto.
        clearbody v.
        clear c i.

        destruct_val vl.
        destruct_val v.

        eexists (mk_exstate _ _ _ _); repeat constructor.
        intros [τ' s''] H.
        cbn in *.

        d_destruct H; try absurd_val.
        auto.
      }
    } {
      left.
      (* TODO: remove copy/paste *)
      destruct c; cbn in n; try tauto. {
        discriminate H.
      } {
        eexists (mk_exstate _ _ _ _); repeat constructor.
        intros [τ' s''] H.
        cbn in *.

        d_destruct H; try absurd_val.
        auto.
      } {
        eexists (mk_exstate _ _ _ _); repeat constructor.
        intros [τ' s''] H.
        cbn in *.

        d_destruct H; try absurd_val.
        auto.
      } {
        eexists (mk_exstate _ _ _ _); repeat constructor.
        intros [τ' s''] H.
        cbn in *.

        d_destruct H; try absurd_val.
        auto.
      } {
        eexists (mk_exstate _ _ _ _); repeat constructor.
        intros [τ' s''] H.
        cbn in *.

        d_destruct H; try absurd_val.
        auto.
      }
    }
  Qed.

  Inductive step_n : forall {τ τ'}, nat -> state τ -> state τ' -> Type :=
  | step_O : forall {τ} (s : state τ),
      step_n O s s
  | step_S : forall {τ0 τ1 τ2} (n : nat) (s0 : state τ0) (s1 : state τ1) (s2 : state τ2),
      s0 --> s1 ->
      step_n n s1 s2 ->
      step_n (S n) s0 s2.

  Reserved Infix "-->*" (at level 84).
  (* Inductive step_star : forall {τ τ'}, state τ -> state τ' -> Type := *)
  (* | step_refl : forall {τ} (s : state τ), *)
  (*     s -->* s *)
  (* | step_one : forall {τ0 τ1 τ2} (s0 : state τ0) (s1 : state τ1) (s2 : state τ2), *)
  (*     s0 --> s1 -> *)
  (*     s1 -->* s2 -> *)
  (*     s0 -->* s2 *)
  (* where "s0 -->* s1" := (step_star s0 s1). *)

  Definition step_star {τ τ'} (s0 : state τ) (s1 : state τ') : Type :=
    {n : nat & step_n n s0 s1}.
  Infix "-->*" := step_star.

  Definition step_refl {τ} (s : state τ) : s -->* s := existT _ O (step_O s).
  Definition step_one {τ0 τ1 τ2} (s0 : state τ0) (s1 : state τ1) (s2 : state τ2)
             (H : s0 --> s1)
             (H0 : s1 -->* s2)
    : s0 -->* s2 :=
    let (n, H1) := H0 in
    existT _ (S n) (step_S n s0 s1 s2 H H1).

  Lemma step_star_trans {τ0 τ1 τ2} (s0 : state τ0) (s1 : state τ1) (s2 : state τ2) :
    s0 -->* s1 ->
    s1 -->* s2 ->
    s0 -->* s2.
  Proof.
    intros [n0 H0] [n1 H1].
    exists (n0 + n1)%nat.
    induction H0; auto.
    eapply step_S; eauto.
  Qed.

  Lemma big_implies_small {τ} (σ : Entropy) (e : expr · τ) (v : val τ) (w : R+) :
    (EVAL σ ⊢ e ⇓ v, w) ->
    forall w0 k,
    {σ' : Entropy &
          mk_state e σ w0 k -->* mk_state v σ' (w0 * w) k}.
  Proof.
    intro.
    induction H; intros. {
      exists σ.
      replace (w0 * 1) with w0 by ring.
      exists O.
      constructor.
    } {
      cbn in *.
      specialize (IHeval1 w3 (kAppFn (πR σ) ea k)).
      specialize (IHeval2 (w3 * w0) (kAppArg (πR (πR σ)) (v_lam body) k)).
      specialize (IHeval3 (w3 * w0 * w1) k).
      destruct IHeval1 as [σ'1 IHeval1].
      destruct IHeval2 as [σ'2 IHeval2].
      destruct IHeval3 as [σ'3 IHeval3].

      exists σ'3.

      eapply step_one; [constructor |].
      eapply step_star_trans; eauto.
      eapply step_one. {
        replace (e_lam body) with (v_lam body : expr · (τa ~> τr)) by auto.
        constructor.
      }
      eapply step_star_trans; eauto.
      eapply step_one; [constructor |].
      rewrite !ennr_mul_assoc.
      auto.
    } {
      cbn in *.

      specialize (IHeval w0 (kFactor k)).
      destruct IHeval as [σ' IHeval].

      exists σ'.

      eapply step_one; [constructor |].
      eapply step_star_trans; eauto.
      eapply step_one; [constructor |].
      rewrite (ennr_mul_comm (finite r rpos) w).
      rewrite ennr_mul_assoc.
      apply step_refl.
    } {
      eexists σ.
      replace (w0 * 1) with w0 by ring.
      eapply step_one; [constructor |].
      apply step_refl.
    } {
      cbn in *.
      specialize (IHeval1 w2 (kPlusL (πR σ) e1 k)).
      specialize (IHeval2 (w2 * w0) (kPlusR (v_real r0) k)).
      destruct IHeval1 as [σ'1 IHeval1].
      destruct IHeval2 as [σ'2 IHeval2].

      exists σ'2.

      eapply step_one; [constructor |].
      eapply step_star_trans; eauto.
      eapply step_one. {
        replace (e_real r0) with (v_real r0 : expr · ℝ) by auto.
        constructor.
      }
      eapply step_star_trans; eauto.
      eapply step_one; [constructor |].
      rewrite <- ennr_mul_assoc.
      apply step_refl.
    }
  Qed.

  (* unabstract relates AM states back to terms (with some entropy manipulation.
     This is needed to be the intermediate correspondance between big and small
     step. *)
  Fixpoint unabstract {τ} (e : expr · τ) (σ : Entropy) (k : kont τ)
    : (expr · τP ⨉ Entropy) :=
    match k in kont τ' return τ = τ' -> (expr · τP ⨉ Entropy) with
    | kHalt => fun τeq => (rew τeq in e, σ)
    | kAppFn σ' ea k' =>
      fun τeq =>
        unabstract (e_app (rew τeq in e) ea) (join σ σ') k'
    | kAppArg σ' vf k' =>
      fun τeq =>
        unabstract (e_app vf (rew τeq in e)) (join σ σ') k'
    | kFactor k' =>
      fun τeq =>
        unabstract (e_factor (rew τeq in e)) σ k'
    | kPlusL σ' er k' =>
      fun τeq =>
        unabstract (e_plus (rew τeq in e) er) (join σ σ') k'
    | kPlusR vl k' =>
      fun τeq =>
        unabstract (e_plus vl (rew τeq in e)) σ k'
    end eq_refl.

End AbstractMachine.
Arguments mk_state {τP τ} c σ w k.

Module AbstractMachineNotations.
  Infix "-->" := (step _) (at level 84).
  Infix "-->*" := (step_star _) (at level 84).
  Notation "s -->^{ n } s'" := (step_n _ n s s') (at level 84).
End AbstractMachineNotations.
Import AbstractMachineNotations.

Lemma ennr_mul_must_be_1 (r r1 : R+) :
  0 < r ->
  r < infinite ->
  r = r * r1 ->
  r1 = 1.
Proof.
  intros.
  destruct r; try contradiction.
  cbn in *.
  destruct r1; revgoals. {
    unfold ennr_mult in H1.
    destruct Req_EM_T; try discriminate.
    subst.
    apply Rlt_irrefl in H.
    contradiction.
  } {
    ennr.
    inject H1.
    eapply Rmult_eq_reg_l. {
      ring_simplify.
      exact (eq_sym H3).
    } {
      apply Rgt_not_eq.
      auto.
    }
  }
Qed.

Fixpoint kont_compose {τi τm τo} (ki : kont τm τi) (ko : kont τo τm) : kont τo τi :=
  match ki with
  | kHalt _ => ko
  | kAppFn _ σ ea ki' => kAppFn _ σ ea (kont_compose ki' ko)
  | kAppArg _ σ vf ki' =>  kAppArg _ σ vf (kont_compose ki' ko)
  | kFactor _ ki' =>  kFactor _ (kont_compose ki' ko)
  | kPlusL _ σ er ki' =>  kPlusL _ σ er (kont_compose ki' ko)
  | kPlusR _ vl ki' =>  kPlusR _ vl (kont_compose ki' ko)
  end.


Lemma extend_kont_step {τ τ' τP τP'} (e : expr · τ) (e' : expr · τ')
      (σ σ' : Entropy)
      (w w' : R+)
      (k : kont τP τ) (k' : kont τP τ') (k'' : kont τP' τP) :
  mk_state e σ w k --> mk_state e' σ' w' k' ->
  mk_state e σ w (kont_compose k k'')  --> mk_state e' σ' w' (kont_compose k' k'').
Proof.
  intros.
  d_destruct H; constructor.
Qed.

Lemma extend_kont_step_star {τ τ' τP τP'} (e : expr · τ) (e' : expr · τ')
      (σ σ' : Entropy)
      (w w' : R+)
      (k : kont τP τ) (k' : kont τP τ') (k'' : kont τP' τP)
      (n : nat) :
  mk_state e σ w k -->^{n} mk_state e' σ' w' k' ->
  mk_state e σ w (kont_compose k k'') -->^{n} mk_state e' σ' w' (kont_compose k' k'').
Proof.
  intros.
  dependent induction H. {
    constructor.
  } {
    destruct s1.
    econstructor; auto.
    apply extend_kont_step; auto.
  }
Qed.

Lemma step_weight_1 {τ τ' τP} {e : expr · τ} {e' : expr · τ'} {σ σ' : Entropy}
      {k : kont τP τ} {k' : kont τP τ'} {w w' : R+} :
  mk_state e σ w k --> mk_state e' σ' w' k' ->
  {wdiff : R+ | w' = w * wdiff /\ 0 < wdiff /\ wdiff < infinite}.
Proof.
  intros.
  assert (0 < 1) by (cbn; exact Rlt_0_1).
  assert (1 < infinite) by (cbn; trivial).
  d_destruct H; try solve [exists 1; split; auto; ring].

  repeat econstructor.
Admitted.

Lemma step_weights {τ τ' τP} {e : expr · τ} {e' : expr · τ'} {σ σ' : Entropy}
      {k : kont τP τ} {k' : kont τP τ'} {w w' : R+} {n : nat} :
  mk_state e σ w k -->^{n} mk_state e' σ' w' k' ->
  {wdiff : R+ & w' = w * wdiff}.
Proof.
  intros.
  move n after τ.
  revert_until n.
  induction n; intros. {
    d_destruct H.
    exists 1.
    ring.
  } {
    d_destruct H.
    destruct s1.
    destruct (IHn _ _ _ _ _ _ _ _ _ _ _ H).
    subst.
    destruct (step_weight_1 s) as [? [? [? ?]]].
    subst.
    eexists.
    rewrite <- ennr_mul_assoc.
    reflexivity.
  }
Qed.

Lemma multiply_step {τ τ' τP e e' σ σ' w w'} {k : kont τP τ} {k' : kont τP τ'} w0 :
  mk_state e σ w k --> mk_state e' σ' w' k' ->
  mk_state e σ (w0 * w) k --> mk_state e' σ' (w0 * w') k'.
Proof.
  intros.
  d_destruct H; try econstructor.
  rewrite ennr_mul_assoc.
  constructor.
Qed.

Lemma multiply_trace {τ τ' τP e e' σ σ' w w' n}
      {k : kont τP τ} {k' : kont τP τ'} w0 :
  mk_state e σ w k -->^{n} mk_state e' σ' w' k' ->
  mk_state e σ (w0 * w) k -->^{n} mk_state e' σ' (w0 * w') k'.
Proof.
  intros.
  move n after τ.
  revert_until n.
  induction n; intros. {
    d_destruct H.
    constructor.
  } {
    d_destruct H.
    destruct s1.
    apply (multiply_step w0) in s.
    econstructor; eauto.
  }
Qed.

Lemma unmultiply_ennr w' {w0} :
  0 < w0 ->
  w0 < infinite ->
  (forall w, w0 * w = w0 * w' -> w = w').
Proof.
  intros Hw0 Hw0' w H.
  destruct w0; try contradiction; cbn in *.
  destruct w, w'; auto. {
    inject H.
    ennr.
    apply (Rmult_eq_reg_l r); auto.
    exact (not_eq_sym (Rlt_not_eq _ _ Hw0)).
  } {
    exfalso.
    unfold ennr_mult in H.
    destruct Req_EM_T; try discriminate.
    contradict e.
    exact (Rlt_not_eq _ _ Hw0).
  } {
    exfalso.
    unfold ennr_mult in H.
    destruct Req_EM_T; try discriminate.
    contradict e.
    exact (Rlt_not_eq _ _ Hw0).
  }
Qed.

Lemma unmultiply_step {τ τ' τP e e' σ σ' w w' w0}
      {k : kont τP τ} {k' : kont τP τ'} :
  0 < w0 ->
  w0 < infinite ->
  mk_state e σ (w0 * w) k --> mk_state e' σ' (w0 * w') k' ->
  mk_state e σ w k --> mk_state e' σ' w' k'.
Proof.
  intros Hw0 Hw0' H.

  pose proof (unmultiply_ennr w' Hw0 Hw0').

  d_destruct H;
    try solve [specialize (H0 _ x);
               subst;
               econstructor].
  rewrite <- ennr_mul_assoc in x.
  specialize (H0 _ x).
  subst.
  constructor.
Qed.

Lemma unmultiply_trace {τ τ' τP e e' σ σ' w w' w0 n}
      {k : kont τP τ} {k' : kont τP τ'} :
  0 < w0 ->
  w0 < infinite ->
  mk_state e σ (w0 * w) k -->^{n} mk_state e' σ' (w0 * w') k' ->
  mk_state e σ w k -->^{n} mk_state e' σ' w' k'.
Proof.
  intros.
  move n after τ.
  revert_until n.
  induction n; intros. {
    d_destruct H1.
    pose proof unmultiply_ennr _ H H0 _ x.
    subst.
    constructor.
  } {
    d_destruct H1.
    destruct s1.
    destruct (step_weight_1 s) as [? [? [? ?]]].
    subst.
    rewrite <- ennr_mul_assoc in *.
    apply (unmultiply_step H H0) in s.
    econstructor; eauto.
  }
Qed.

Lemma small_implies_big {τ τP} (e : expr · τ) (σ σP : Entropy) (k : kont τP τ)
      (v : val τP) (w : R+) (eP : expr · τP) :
  (eP, σP) = unabstract _ e σ k ->
  mk_state e σ 1 k -->* mk_state v σP w (kHalt _) ->
  (EVAL σP ⊢ eP ⇓ v, w).
Proof.
  intros Hu [n H].
  move n after τ.

  enough ((forall w0,
              mk_state e σ w0 k -->^{ n} mk_state v σP (w0 * w) (kHalt τP)) ->
          EVAL σP ⊢ eP ⇓ v, w).
  {
    apply H0.
    intros.
    replace w0 with (w0 * 1) at 1 by ring.
    apply multiply_trace; auto.
  }

  intros.
  clear H.
  rename H0 into H.

  revert_until n.
  induction n; intros. {
    specialize (H 1).
    d_destruct H.
    enough (w = 1) by (subst; constructor).
    destruct w. {
      inject x.
      ennr.
      ring_simplify in H0.
      auto.
    } {
      unfold ennr_mult in x.
      destruct Req_EM_T; try discriminate.
      contradict e.
      apply not_eq_sym, R1_neq_R0.
    }
  } {
    evar (ww : R+).
    specialize (H ww).
    d_destruct H.
    destruct s1.
    (* destruct (step_weight_1 s) as [? [? [? ?]]]. *)
    (* subst. *)
    pose proof (step_weights H).
    destruct H0 as [w1 ?].
    rewrite e0 in *.

    replace w0 with (w0 * 1) in H at 1 by ring.
    apply unmultiply_trace in H.
    specialize (IHn τ1 τP c σ0 σP k0 v (w0 * w1) eP).

    apply IHn; revgoals. {
      intros.
      replace w2 with (w2 * 1) at 1 by ring.
      apply multiply_trace.
    }

    (* assert (0 < w0 * x). { *)
    (*   destruct w0, x; try contradiction. *)
    (*   unfold ennr_mult. *)
    (*   cbn. *)
    (*   apply Rmult_lt_0_compat; auto. *)
    (* } *)
    (* specialize (IHn H0); clear H0. *)
    (* assert (w0 * x < infinite). { *)
    (*   destruct w0, x; try contradiction. *)
    (*   auto. *)
    (* } *)
    (* specialize (IHn H0); clear H0. *)

    enough ((eP, σP) = unabstract τP c σ0 k0). {
      replace w0 with (w0 * 1) in H at 1 by ring.
      apply unmultiply_trace in H; auto.
      (* rewrite ennr_mul_assoc in H. *)

      specialize (IHn H0 H).
      apply IHn.
      assert (w = x * x0). {
        revert Hw0 Hw1 H1 H2 e0.
        clear.
        intros.
        destruct w0, x; try contradiction.
        cbn in *.
        unfold ennr_mult in *.
        destruct w, x0; cbn in *. {
          ennr.
          inject e0.
          apply (Rmult_eq_reg_l r). {
            rewrite <- Rmult_assoc.
            auto.
          } {
            apply not_eq_sym.
            apply Rlt_not_eq.
            auto.
          }
        } {
          exfalso.
          destruct Req_EM_T; try discriminate.
          inject e0.
          contradict e.
          apply Rlt_not_eq.
          apply Rmult_lt_0_compat; auto.
        } {
          exfalso.
          destruct Req_EM_T; try discriminate.
          contradict e.
          apply Rlt_not_eq.
          auto.
        } {
          destruct (Req_EM_T 0 r0); auto.
          contradict e.
          apply Rlt_not_eq.
          auto.
        }
      }
      subst.
      enough (w = x * x0). {
        subst.
        apply IHn.
      }
    }



    specialize (IHn _ _ _ _ _ _ _ _ _ _ _ _ Heqp H).
  }


Lemma small_implies_big {τ} (σ : Entropy) (e : expr · τ) (v : val τ) (w w0 : R+) :
    0 < w0 ->
    w0 < infinite ->
    {σ' : Entropy &
          mk_state e σ w0 (kHalt τ) -->* mk_state v σ' (w0 * w) (kHalt τ)} ->
  (EVAL σ ⊢ e ⇓ v, w).
Proof.
  intros Hw0 Hw0' [σ' [n H]].

  assert (forall τP (k : kont τP τ) , mk_state e σ w0 k -->^{n} mk_state v σ' (w0 * w) k). {
    intros.
    apply extend_kont_step_star with (k0 := kHalt τ) (k' := kHalt τ).
    auto.
  }
  clear H.
  rename H0 into H.



  move n after τ.
  revert_until n.
  induction n; intros. {
    specialize (H _ (kHalt _)).
    d_destruct H.
    replace w with 1 by (symmetry; eapply ennr_mul_must_be_1; eauto).
    constructor.
  } {
    pose proof (H _ (kHalt _)).
    d_destruct H0.
    specialize (IHn _ _ _ _ _ _ _ _ _ H0).
  }

  refine
    (match H with
     | step_refl _ _ => _
     | step_one _ _ _ _ _ _ => _
     end).






  set (τP := τ).
  set (k := kHalt τP).
  replace (kHalt τ) with (kont_compose (kHalt τ) k) in H by auto.
  clearbody k τP.

  dependent induction H. {
    replace w with 1 by (symmetry; eapply ennr_mul_must_be_1; eauto).
    constructor.
  } {
    destruct s1.
    specialize (IHstep_star σ0 e).
  }
Qed.





  (* unabstract relates AM states back to terms (with some entropy manipulation.
     This is needed to be the intermediate correspondance between big and small
     step. *)
  Fixpoint unabstract {τ} (e : expr · τ) (σ : Entropy) (k : kont τ)
    : (expr · τP ⨉ Entropy) :=
    match k in kont τ' return τ = τ' -> (expr · τP ⨉ Entropy) with
    | kHalt => fun τeq => (rew τeq in e, σ)
    | kAppFn σ' ea k' =>
      fun τeq =>
        unabstract (e_app (rew τeq in e) ea) (join σ σ') k'
    | kAppArg σ' vf k' =>
      fun τeq =>
        unabstract (e_app vf (rew τeq in e)) (join σ σ') k'
    | kFactor k' =>
      fun τeq =>
        unabstract (e_factor (rew τeq in e)) σ k'
    | kPlusL σ' er k' =>
      fun τeq =>
        unabstract (e_plus (rew τeq in e) er) (join σ σ') k'
    | kPlusR vl k' =>
      fun τeq =>
        unabstract (e_plus vl (rew τeq in e)) σ k'
    end eq_refl.

  Definition evals_to' {τ} (s : state τ) (res : result) :=
    {n : nat & step_n n s = inr res}.
End AbstractMachine.

Lemma split_the_machine {τP τ}
      (e : expr · τ)
      (σ : Entropy)
      (k : kont τP τ)
      (w : R+) :
  forall vP wP,
    evals_to' _ (mk_state _ _ e σ w k) (Some (vP, wP)) ->
    { vwI : (val τ ⨉ R+) &
            (evals_to' _ (mk_state _ _ e σ w (kHalt _)) (Some vwI))
              ⨉ (evals_to'
                   _
                   (mk_state _ _ (fst vwI) dummy_entropy (snd vwI) k)
                   (Some (vP, wP)))}.
Proof.
  intros.
  destruct H as [n H].
  revert_until e.
  revert τP.
  dependent induction e; intros. {
    exists (v_real r, w).
    split. {
      exists 1%nat.
      auto.
    } {
      cbn.
      exists n.
      destruct n; try discriminate.
      apply H.
    }
  } {
    exists (v_lam e, w).
    split. {
      exists 1%nat.
      auto.
    } {
      cbn.
      exists n.
      destruct n; try discriminate.
      apply H.
    }
  } {

  }
Qed.


Lemma compose_small {τP τ}
      (e : expr · τ)
      (σ0 σdummy : Entropy)
      (k : kont τP τ)
      (w0 : R+) :
  forall v w v' w',
    evals_to' _ (mk_state _ _ e σ0 w0 (kHalt _)) (Some (v, w)) ->
    evals_to' _ (mk_state _ _ v σdummy w k) (Some (v', w')) ->
    evals_to' _ (mk_state _ _ e σ0 w0 k) (Some (v', w')).
Proof.
  intros.
  revert_until e.
  dependent induction e; intros. {
    destruct H0 as [n1 H1], H as [n0 H0].
    destruct n0, n1; try discriminate.
    exists (S n1)%nat.
    destruct_val v.
    cbn in *.
    inject H0.
    auto.
  } {
    destruct H0 as [n1 H1], H as [n0 H0].
    destruct n0, n1; try discriminate.
    exists (S n1)%nat.
    destruct_val v.
    cbn in *.
    d_destruct H0.
    auto.
  } {
    specialize (IHe1 (πL σ0) σdummy (kAppFn _ (πR σ0) e2 k) w0).
    specialize (IHe2 (πL (πR σ0)) σdummy (kAppArg _ (πR (πR σ0)) _ k)).
    cbn in H0.
    cbn.
  }
Qed.


Lemma small_implies_big {τ} (s : state τ) (v : val τP) (w : R+) :
  let (e, σ, w, k) := s in
  let (eP, σP) := unabstract e σ k in
  evals_to' s (Some (v, w)) ->
  (EVAL σP ⊢ eP ⇓ v, w).
Proof.
  destruct s.
  revert k σ w0 v w.
  dependent induction c; intros. {
    cbn.
  } {
  }
Qed.

Lemma big_implies_small {τ} (s : state τ) (v : val τP) (w : R+) :
  let (e, σ, w, k) := s in
  let (eP, σP) := unabstract e σ k in
  (EVAL σP ⊢ eP ⇓ v, w) ->
  evals_to' s (Some (v, w)).
Proof.
  destruct s.
  remember (unabstract _ _ _).
  destruct p.
  intros.
  dependent induction H.
  exists 1%nat.
  }
Qed.

End AbstractMachine.

Definition inject {τ} (e : expr · τ) (σ : Entropy) : state τ τ :=
  mk_state τ τ e σ 1 (kHalt _).

Definition evals_to {τ} (e : expr · τ) (σ : Entropy) (v : val τ) (w : R+) :=
  evals_to' _ (inject e σ) (Some (v, w)).

intros.

induction H. {
  destruct_val v;
    subst;
    cbn;
    exists 1%nat;
    auto.
} {
  admit.
} {
  admit.
} {
  exists 1%nat; auto.
} {
  destruct IHeval1 as [n_1 ev_1].
  destruct IHeval2 as [n_2 ev_2].
}
Qed.
