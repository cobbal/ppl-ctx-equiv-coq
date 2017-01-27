Require Import Reals.
Require Import List.
Require Import Ensembles.
Require Import Coq.Logic.JMeq.
Require Import utils.
Require Import syntax.
Require Import RelationClasses.
Require Import chain.

Local Open Scope ennr.

Inductive kont_frame : Ty -> Ty -> Type :=
| kAppFn {τa τr} (σ : Entropy) (ea : expr · τa)
  : kont_frame (τa ~> τr) τr
| kAppArg {τa τr} (σ : Entropy) (vf : val (τa ~> τr))
  : kont_frame τa τr
| kFactor
  : kont_frame ℝ ℝ
| kPlusL (σ : Entropy) (er : expr · ℝ)
  : kont_frame ℝ ℝ
| kPlusR (vl : val ℝ)
  : kont_frame ℝ ℝ
.

Section AbstractMachine.
  (* τP is the type of the whole program *)
  Variables τP : Ty.

  (* a continuation is a stack of continuation frames. Sometimes it's convenient
     to look at it as a top down stack, and other times it's a bottom-up stack.
     The 'kont' type is intended as a innermost to outermost stack (head of the
     list will be the next continuation that gets run). *)
  Definition kont τ := chain kont_frame τ τP.
  Definition kHalt : kont τP := chain_nil.

  (* rev_kont is the other way around (head of the list is the last continuation to run). *)
  Definition rev_kont τ := chain (@flip _ _ Type kont_frame) τP τ.
  (* the explicit Type is needed above so that something doesn't get lowered to
     Set for some stupid reason I don't understand *)

  Inductive state τ :=
  | mk_state (c : expr · τ) (σ : Entropy) (k : kont τ)
  .
  Arguments mk_state {τ} c σ k.

  Inductive step : forall {τ τ'}, state τ -> state τ' -> R+ -> Type :=
  (* not a value, destruct the expression *)
  | step_app : forall {τa τr ef ea σ k},
      (@mk_state τr (e_app ef ea) σ k -->
       @mk_state (τa ~> τr) ef (πL σ) (kAppFn (πR σ) ea ::: k)) 1
  | step_factor : forall {e σ k},
      (@mk_state ℝ (e_factor e) σ k -->
       @mk_state ℝ e σ (kFactor ::: k)) 1
  | step_sample : forall {σ k},
      (@mk_state ℝ e_sample σ k -->
       @mk_state ℝ (v_real (proj1_sig (σ O))) σ k) 1
  | step_plus : forall {el er σ k},
      (@mk_state ℝ (e_plus el er) σ k -->
       @mk_state ℝ el (πL σ) (kPlusL (πR σ) er ::: k)) 1

  (* is a value, destruct the continuation *)
  | step_k_app_fn : forall {τa τr} {vf : val (τa ~> τr)} {ea σ_unused σ k},
      (@mk_state (τa ~> τr) vf σ_unused (kAppFn σ ea ::: k) -->
       @mk_state τa ea (πL σ) (kAppArg (πR σ) vf ::: k)) 1
  | step_k_app_arg : forall {τa τr} {va : val τa} {body σ_unused σ k},
      (@mk_state τa va σ_unused (kAppArg σ (v_lam body) ::: k) -->
       @mk_state τr (proj1_sig (ty_subst1 body va)) (πL σ) k) 1
  | step_k_factor : forall {r σ_unused k} (rpos : (0 <= r)%R),
      (@mk_state ℝ (e_real r) σ_unused (kFactor ::: k) -->
       @mk_state ℝ (e_real r) σ_unused k) (finite r rpos)
  | step_k_plus_l : forall {vl : val ℝ} {er σ_unused σ k},
      (@mk_state ℝ vl σ_unused (kPlusL σ er ::: k) -->
       @mk_state ℝ er (πL σ) (kPlusR vl ::: k)) 1
  | step_k_plus_r : forall {rl rr : R} {σ k},
      (@mk_state ℝ (e_real rr) σ (kPlusR (v_real rl) ::: k) -->
       @mk_state ℝ (e_real (rl + rr)%R) σ k) 1
  where "s0 --> s1" := (step s0 s1).

  Reserved Notation "s -->^[ n ] t" (at level 84).
  Inductive step_n : forall {τ τ'}, nat -> state τ -> state τ' -> R+ -> Type :=
  | step_O : forall {τ} (s : state τ),
      (s -->^[O] s) 1
  | step_S : forall {τ0 τ1 τ2} {n : nat} {s0 : state τ0} {s1 : state τ1} {s2 : state τ2} {w0 w1 : R+},
      (s0 --> s1) w0 ->
      (s1 -->^[n] s2) w1 ->
      (s0 -->^[S n] s2) (w0 * w1)
  where "s -->^[ n ] t" := (step_n n s t).

  Reserved Infix "-->*" (at level 84).

  Definition step_star {τ τ'} (s0 : state τ) (s1 : state τ') (w : R+) : Type :=
    {n : nat & (s0 -->^[n] s1) w}.
  Infix "-->*" := step_star.

  Definition step_refl {τ} (s : state τ) : (s -->* s) 1 := existT _ O (step_O s).
  Definition step_one {τ0 τ1 τ2} {s0 : state τ0} {s1 : state τ1} {s2 : state τ2} {w0 w1}
             (H0 : (s0 --> s1) w0)
             (H1 : (s1 -->* s2) w1)
    : (s0 -->* s2) (w0 * w1) :=
    let (n, H1) := H1 in
    existT _ (S n) (step_S H0 H1).

  Lemma step_star_trans {τ0 τ1 τ2} {s0 : state τ0} {s1 : state τ1} {s2 : state τ2} {w0 w1} :
    (s0 -->* s1) w0 ->
    (s1 -->* s2) w1 ->
    (s0 -->* s2) (w0 * w1).
  Proof.
    intros [n0 H0] [n1 H1].
    exists (n0 + n1)%nat.
    induction H0. {
      rewrite ennr_mul_1_l.
      auto.
    } {
      rewrite <- ennr_mul_assoc.
      eapply step_S; eauto.
    }
  Qed.

  Lemma big_implies_small' {τ} (σ : Entropy) (e : expr · τ) (v : val τ) (w : R+) :
    (EVAL σ ⊢ e ⇓ v, w) ->
    forall k,
    {σ' : Entropy &
          (mk_state e σ k -->* mk_state v σ' k) w}.
  Proof.
    intro.
    induction H; intros. {
      exists σ.
      apply step_refl.
    } {
      specialize (IHeval1 (kAppFn (πR σ) ea ::: k)).
      specialize (IHeval2 (kAppArg (πR (πR σ)) (v_lam body) ::: k)).
      specialize (IHeval3 k).
      destruct IHeval1 as [σ'1 IHeval1].
      destruct IHeval2 as [σ'2 IHeval2].
      destruct IHeval3 as [σ'3 IHeval3].

      exists σ'3.

      rewrite <- ennr_mul_1_l.
      eapply step_one; [constructor |].

      eapply step_star_trans; eauto.
      eapply step_star_trans; eauto.
      rewrite <- ennr_mul_1_l.
      eapply step_one; [constructor |].

      replace w1 with (w1 * (1 * 1)) by ring.
      eapply step_star_trans; eauto.

      eapply step_one; [constructor |].
      apply step_refl.
    } {
      specialize (IHeval (kFactor ::: k)).
      destruct IHeval as [σ' IHeval].

      exists σ'.

      rewrite <- ennr_mul_1_l.
      eapply step_one; [constructor |].
      rewrite ennr_mul_comm.
      eapply step_star_trans; eauto.
      rewrite <- ennr_mul_1_r.
      eapply step_one; [constructor |].
      apply step_refl.
    } {
      eexists σ.
      rewrite <- ennr_mul_1_l.
      eapply step_one; [constructor |].
      apply step_refl.
    } {
      cbn in *.
      specialize (IHeval1 (kPlusL (πR σ) e1 ::: k)).
      specialize (IHeval2 (kPlusR (v_real r0) ::: k)).
      destruct IHeval1 as [σ'1 IHeval1].
      destruct IHeval2 as [σ'2 IHeval2].

      exists σ'2.

      rewrite <- ennr_mul_1_l.
      eapply step_one; [constructor |].
      eapply step_star_trans; eauto.
      rewrite <- ennr_mul_1_l.
      rewrite !rewrite_v_real.
      eapply step_one; [constructor |].
      rewrite <- ennr_mul_1_r.
      eapply step_star_trans; eauto.
      rewrite <- ennr_mul_1_l.
      eapply step_one; [constructor |].
      apply step_refl.
    }
  Qed.
End AbstractMachine.

Arguments mk_state {τP τ} c σ k.

Module AbstractMachineNotations.
  Infix "-->" := (step _).
  Infix "-->*" := (step_star _) (at level 84).
  Notation "s -->^[ n ] t" := (step_n _ n s t) (at level 84).
End AbstractMachineNotations.
Import AbstractMachineNotations.


(* In order to get a big-step derivation from a small-step one, we're going to
   need to be able to big-step the intermediate states. To do this, we simply
   plug the expression back into the configuration and lie about entropy in ways
   that the big step relation won't notice. *)

(* Some arbitrary entropy will be needed when shoving values back into
   expressions to be big-stepped. Since it won't be read, the value is
   intentionally set to be opaque. *)
Lemma dummy_entropy : Entropy.
Proof.
  exists 0%R.
  split. {
    apply Rle_refl.
  } {
    apply Rlt_le.
    apply Rlt_0_1.
  }
Qed.

(* First, we plug an expression/entropy into single frame. We will then lift it
   two different ways to an entire continuation (forwards and reverse). Most of
   the ugliness comes from fighting dependent types, the only really interesting
   part is the `dummy_entropy` that gets thrown in. *)
Definition unabstract_frame {τo τi} (eσ : expr · τi * Entropy) (f : kont_frame τi τo)
  : (expr · τo * Entropy) :=
  match f in (kont_frame τi' τo') return τi = τi' -> (expr · τo' * Entropy) with
  | kAppFn σ' ea => fun Hτi => (e_app (rew Hτi in (fst eσ)) ea,
                                join (snd eσ) σ')
  | kAppArg σ' vf => fun Hτi => (e_app vf (rew Hτi in (fst eσ)),
                                 join dummy_entropy (join (snd eσ) σ'))
  | kFactor => fun Hτi => (e_factor (rew Hτi in (fst eσ)),
                           (snd eσ))
  | kPlusL σ' er => fun Hτi => (e_plus (rew Hτi in (fst eσ)) er,
                                join (snd eσ) σ')
  | kPlusR vl => fun Hτi => (e_plus vl (rew Hτi in (fst eσ)),
                             join dummy_entropy (join (snd eσ) dummy_entropy))
  end eq_refl.

Fixpoint unabstract_rev {τo τi} (eσ : expr · τi * Entropy) (rk : rev_kont τo τi)
  : (expr · τo * Entropy) :=
  match rk in chain _ τo' τi' return (τi = τi' -> expr · τo' * Entropy) with
  | chain_nil => fun Hτi => rew [fun ti => (expr · ti * Entropy)%type] Hτi in eσ
  | @chain_cons _ _ τo' τm τi' f rk' =>
    fun Hτi =>
      unabstract_frame (unabstract_rev eσ (rew <- Hτi in rk') : expr · τm * Entropy) f
  end eq_refl.

Definition unabstract {τo τi} (eσ : expr · τi * Entropy) (k : kont τo τi)
  : (expr · τo * Entropy) := unabstract_rev eσ (chain_rev k).

Fixpoint unabstract' {τP τ} (eσ : expr · τ * Entropy) (k : kont τP τ)
  : (expr · τP * Entropy) :=
  match k in chain _ τ' τP'
        return τ = τ' -> (expr · τP' * Entropy) with
  | chain_nil =>
    fun Hτ =>
      (rew [fun t => (expr · t * Entropy)%type] Hτ in eσ)
  | @chain_cons _ _ τ0 τ1 τP' f k' =>
    fun Hτ =>
      unabstract' (unabstract_frame eσ (rew <-[fun t => kont_frame t τ1] Hτ in f)) k'
  end eq_refl.

Lemma unabstract'_compose {τo τm τi} (eσ : expr · τi * Entropy)
      (ko : kont τo τm) (ki : kont τm τi) :
  unabstract' (unabstract' eσ ki) ko = unabstract' eσ (ki +++ ko).
Proof.
  revert eσ.
  induction ki; cbn; auto.
Qed.

Lemma unabstracts_eq {τo τi} eσ (k : kont τo τi) : unabstract eσ k = unabstract' eσ k.
Proof.
  revert eσ.
  induction k using rev_chain_rect; intros; auto.

  pose proof unabstract'_compose eσ (x ::: chain_nil) k.
  unfold chain_snoc in *.
  rewrite <- H.
  rewrite <- IHk.
  cbn.

  unfold unabstract.
  rewrite chain_rev_app_distr.
  auto.
Qed.

Lemma unabstract_compose {τo τm τi} (eσ : expr · τi * Entropy)
      (ko : kont τo τm) (ki : kont τm τi) :
  unabstract (unabstract eσ ki) ko = unabstract eσ (ki +++ ko).
Proof.
  rewrite !unabstracts_eq.
  apply unabstract'_compose.
Qed.


(* guts of an assert that got migrated to a lemma.
   TODO: clean up and figure out what it really does. *)
Lemma small_big_lemma_lemma {τP τ}
      {e e' : expr · τ}
      {σ σ' : Entropy}
      {k' : kont τP τ}
      {eP : expr · τP}
      {σP : Entropy}
      (Heqp : (eP, σP) = unabstract (e, σ) k')
      {e'P : expr · τP}
      {σ'P : Entropy}
      (Heqp0 : (e'P, σ'P) = unabstract (e', σ') k')
      {vP : val τP}
      {w0 w1 wdiff : R+}
      (Hw : w0 = wdiff * w1)
      (e_e'_match : forall v w, EVAL σ' ⊢ e' ⇓ v, w -> EVAL σ ⊢ e ⇓ v, wdiff * w)
      (HP : EVAL σ'P ⊢ e'P ⇓ vP, w1)
  : EVAL σP ⊢ eP ⇓ vP, w0.
Proof.
  subst.
  dependent induction k' using rev_chain_rect. {
    cbn in *.
    autoinjections.
    auto.
  } {
    unfold chain_snoc in *.
    rewrite <- unabstract_compose in Heqp, Heqp0.
    cbn in *.

    specialize (IHk' e e').

    dep_destruct x;
      cbn in *;
      inject Heqp;
      inject Heqp0;
      remember (unabstract (e, _) _) in *;
      remember (unabstract (e', _) _) in *;
      destruct p as [eP σP], p0 as [e'P σ'P];
      cbn in *;
      specialize (IHk' _ _ eq_refl _ _ eq_refl);
      dep_destruct HP; try absurd_val.
    {
      replace (_ * _) with ((wdiff * w0) * w1 * w2) by ring.
      econstructor; π_join; eauto.
    } {
      replace (_ * _) with (w0 * (wdiff * w1) * w2) by ring.
      econstructor; π_join; eauto.
    } {
      replace (_ * _) with (finite r rpos * (wdiff * w)) by ring.
      econstructor; π_join; eauto.
    } {
      replace (_ * _) with ((wdiff * w0) * w1) by ring.
      econstructor; π_join; eauto.
    } {
      replace (_ * _) with (w0 * (wdiff * w1)) by ring.
      econstructor; π_join; eauto.
    }
  }
Qed.


(* essentially, if a state big-steps to something, after a single small step it
   should big-step to the same value it originally did. *)
Lemma small_big_lemma {τP}
      {τ} (e : expr · τ) (σ : Entropy) (k : kont τP τ)
      {τ'} (e' : expr · τ') (σ' : Entropy) (k' : kont τP τ') :
  let (eP, σP) := unabstract (e, σ) k in
  let (e'P, σ'P) := unabstract (e', σ') k' in
  forall (v : val τP) (w0 w1 : R+),
    (mk_state e σ k --> mk_state e' σ' k') w0 ->
    (EVAL σ'P ⊢ e'P ⇓ v, w1) ->
    (EVAL σP ⊢ eP ⇓ v, w0 * w1).
Proof.
  rewrite !unabstracts_eq.

  remember (unabstract' (e, _) _).
  remember (unabstract' (e', _) _).
  destruct p as [eP σP], p0 as [e'P σ'P].
  intros.

  (* ugh *)
  dep_destruct H;
    cbn in *;
    rewrite ?join_πL_πR, ?ennr_mul_1_l, ?rewrite_v_real in *;
    try solve [
          rewrite ?ennr_mul_1_l in *;
          rewrite <- Heqp in Heqp0;
          inject Heqp0;
          auto];
    try rewrite <- unabstracts_eq in Heqp, Heqp0;
    eapply small_big_lemma_lemma; eauto;
      try solve [symmetry; apply ennr_mul_1_l];
      intros;
      rewrite ?ennr_mul_1_l;
      try (destruct (invert_eval_val H); subst).
  {
    constructor.
  } {
    dep_destruct H; try absurd_val.
    destruct (invert_eval_val H); subst.
    repeat econstructor; π_join; eauto.
  } {
    replace w with (1 * 1 * w) by ring.
    rewrite rewrite_v_lam.
    repeat econstructor; π_join; eauto.
  } {
    econstructor; eauto.
  } {
    dep_destruct H; try absurd_val.
    destruct (invert_eval_val H); subst.
    repeat econstructor; π_join; eauto.
  } {
    replace 1 with (1 * 1) by ring.
    repeat econstructor; eauto.
  }
Qed.

Lemma small_implies_big' {τ τP} (e : expr · τ) (σ σ_unused : Entropy) (k : kont τP τ)
      (v : val τP) (w : R+) :
  let (eP, σP) := unabstract (e, σ) k in
  (mk_state e σ k -->* mk_state v σ_unused (kHalt _)) w ->
  (EVAL σP ⊢ eP ⇓ v, w).
Proof.
  remember (unabstract _ _).
  destruct p as [eP σP].

  intros [n ?].
  move n after τ.
  reverse.
  induction n; intros. {
    dep_destruct s.
    constructor.
  } {
    dep_destruct s.
    destruct s1 as [e' σ' k'].
    pose proof small_big_lemma e σ k e' σ' k'.
    rewrite <- Heqp in *.
    remember (unabstract _ k').
    destruct p as [e'P σ'P].
    apply H; auto.
    eapply IHn; eauto.
  }
Qed.

Definition evals_to {τ} σ (e : expr · τ) (v : val τ) (w : R+) :=
  {σ' : Entropy & (mk_state e σ (kHalt τ) -->* mk_state v σ' (kHalt τ)) w}.

Lemma small_implies_big {τ} (σ : Entropy) (e : expr · τ) (v : val τ) (w : R+) :
  evals_to σ e v w ->
  (EVAL σ ⊢ e ⇓ v, w).
Proof.
  intros [σ' ?].
  apply (small_implies_big' e σ σ' (kHalt τ)).
  assumption.
Qed.

Lemma big_implies_small {τ} (σ : Entropy) (e : expr · τ) (v : val τ) (w : R+) :
  (EVAL σ ⊢ e ⇓ v, w) ->
  evals_to σ e v w.
Proof.
  intros.
  apply big_implies_small'.
  assumption.
Qed.

Require Import determinism.

Inductive evals_to_dec_result {τ} (e : expr · τ) (σ : Entropy) :=
| evals_to_dec_yes v w (steps : evals_to σ e v w)
| evals_to_dec_no (H : forall v w, evals_to σ e v w -> False).
Arguments evals_to_dec_yes {_ _ _} _ _ _.
Arguments evals_to_dec_no {_ _ _} _.

Lemma evals_to_dec {τ} (e : expr · τ) (σ : Entropy) : evals_to_dec_result e σ.
Proof.
  destruct (eval_dec e σ). {
    apply (evals_to_dec_yes v w).
    apply big_implies_small.
    apply ev.
  } {
    apply evals_to_dec_no.
    intros.
    specialize (not_ex v w).
    contradict not_ex.
    apply small_implies_big.
    apply X.
  }
Qed.

Definition ev' {τ} (e : expr · τ) σ : option (val τ) :=
  match evals_to_dec e σ with
  | evals_to_dec_yes v w _ => Some v
  | evals_to_dec_no _ => None
  end.

Definition ew' {τ} (e : expr · τ) σ : R+ :=
  match evals_to_dec e σ with
  | evals_to_dec_yes v w _ => w
  | evals_to_dec_no _ => 0
  end.

(* just to see how stepping through ev' and ew' looks... *)
Lemma ew'_is_finite {τ} (e : expr · τ) σ :
  ew' e σ <> infinite.
Proof.
  intros.
  unfold ew'.
  destruct evals_to_dec; auto. {
    destruct steps as [σ' [n steps]].
    induction steps. {
      discriminate.
    } {
      destruct w1; [| contradiction (IHsteps eq_refl)].
      destruct s; unfold ennr_mult; cbn; discriminate.
    }
  } {
    discriminate.
  }
Qed.
