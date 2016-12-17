Require Import Reals.
Require Import List.
Require Import Ensembles.
Require Import Coq.Logic.JMeq.
Require Import utils.
Require Import syntax.
Require Import RelationClasses.

Local Open Scope ennr.

(* like a list, but with dependent types that must match between pairs *)
Inductive chain {X} {P : X -> X -> Type} : X -> X -> Type :=
| chain_nil {A : X} : chain A A
| chain_cons {A B C : X} :
    P A B -> chain B C -> chain A C
.

(* rev_list_ind *)
(*      : forall (A : Type) (P : list A -> Prop), *)
(*        P Datatypes.nil -> *)
(*        (forall (a : A) (l : list A), P (rev l) -> P (rev (a :: l))) -> forall l : list A, P (rev l) *)
(* chain_rect *)
(*      : forall (X : Type) (P : X -> X -> Type) (P0 : forall x x0 : X, chain x x0 -> Type), *)
(*        (forall A : X, P0 A A chain_nil) -> *)
(*        (forall (A B C : X) (p : P A B) (c : chain B C), P0 B C c -> P0 A C (chain_cons p c)) -> *)
(*        forall (y y0 : X) (c : chain y y0), P0 y y0 c *)

Arguments chain {X} P _ _.
Infix ":::" := chain_cons (at level 60, right associativity).

Fixpoint chain_app {X} {P : X -> X -> Type} {A B C}
         (c : chain P A B) (c' : chain P B C) : chain P A C :=
  match c in (chain _ A' B') return (B = B' -> chain P A' C) with
  | chain_nil => fun HB => rew[fun B => chain P B C] HB in c'
  | chain_cons x xs =>
    fun HB =>
    chain_cons x (chain_app xs (rew[fun B => chain P B C] HB in c'))
  end eq_refl.
Infix "+++" := chain_app (right associativity, at level 60).

Theorem chain_app_nil_r {X} {P : X -> X -> Type} {A B}
      (c : chain P A B) :
  c +++ chain_nil = c.
Proof.
  induction c; auto.
  cbn.
  rewrite IHc.
  auto.
Qed.

Theorem chain_app_assoc {X} {P : X -> X -> Type} {A B C D : X}
      (c0 : chain P A B) (c1 : chain P B C) (c2 : chain P C D) :
  c0 +++ (c1 +++ c2) = (c0 +++ c1) +++ c2.
Proof.
  induction c0; auto.
  cbn.
  rewrite IHc0.
  auto.
Qed.

Definition chain_snoc {X} {P : X -> X -> Type} {A B C : X} :
  chain P A B -> P B C -> chain P A C :=
  fun c x => c +++ x ::: chain_nil.

Fixpoint chain_rev {X} {P : X -> X -> Type} {A B}
         (c : chain P A B) : chain (flip P) B A :=
  match c with
  | chain_nil => chain_nil
  | chain_cons x xs => chain_snoc (chain_rev xs) x
  end.

Lemma chain_rev_app_distr {X} {P : X -> X -> Type} {A B C}
      (c0 : chain P A B) (c1 : chain P B C)
  : chain_rev (c0 +++ c1) = chain_rev c1 +++ chain_rev c0.
Proof.
  induction c0. {
    cbn.
    rewrite chain_app_nil_r.
    auto.
  } {
    cbn in *.
    rewrite IHc0.
    setoid_rewrite chain_app_assoc.
    auto.
  }
Qed.

Lemma chain_rev_involutive {X} {P : X -> X -> Type} {A B}
      (c : chain P A B)
  : c = chain_rev (chain_rev c).
Proof.
  induction c; auto.
  cbn.
  unfold chain_snoc.
  rewrite chain_rev_app_distr.
  cbn in *.
  rewrite <- IHc.
  auto.
Qed.

Lemma rev_chain_rect {X} {P : X -> X -> Type}
      (motive : forall A B, chain P A B -> Type)
      (case_nil : forall A, motive A A chain_nil)
      (case_snoc : forall A B C (x : P B C) (c : chain P A B),
          motive A B c -> motive A C (chain_snoc c x))
  : forall {A B} (c : chain P A B), motive A B c.
Proof.
  intros.
  rewrite (chain_rev_involutive c).
  set (chain_rev c).
  clearbody c0.
  clear c.
  induction c0; cbn; auto.
Qed.

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
  Definition result := option (val τP ⨉ R+).

  Definition kont τ := chain kont_frame τ τP.
  Definition kHalt : kont τP := chain_nil.
  (* the explicit Type is needed here so that something doesn't get lowered to
     set for some stupid reason I don't understand *)
  Definition rev_kont τ := chain (@flip _ _ Type kont_frame) τP τ.

  Lemma
    kont_rect' (P : forall τ : Ty, kont τ -> Type)
    (case_halt : P τP kHalt)
    (case_app_fn :
       forall (τa τr : Ty) (σ : Entropy) (ea : expr · τa) (k : kont τr),
         P τr k -> P (τa ~> τr) (kAppFn σ ea ::: k))
    (case_app_arg :
       forall (τa τr : Ty) (σ : Entropy) (vf : val (τa ~> τr)) (k : kont τr),
         P τr k -> P τa (kAppArg σ vf ::: k))
    (case_factor :
       forall k : kont ℝ,
         P ℝ k -> P ℝ (kFactor ::: k))
    (case_plus_l :
       forall (σ : Entropy) (er : expr · ℝ) (k : kont ℝ),
         P ℝ k -> P ℝ (kPlusL σ er ::: k))
    (case_plus_r :
       forall (vl : val ℝ) (k : kont ℝ),
         P ℝ k -> P ℝ (kPlusR vl ::: k))
    : forall {τ} k, P τ k.
  Proof.
    refine (fix F τ (k : kont τ) {struct k} : P τ k :=
              match k as k' in (chain _ τ' τP')
                    return (τ' = τ -> τP' = τP -> k' ~= k -> P τ k) with
              | chain_nil => fun Hτ HτP Hk => _
              | f ::: k'' => fun Hτ HτP Hk => _
              end eq_refl eq_refl JMeq_refl).
    {
      repeat subst.
      apply case_halt.
    } {
      repeat subst.
      specialize (F _ k'').
      destruct f; auto.
    }
  Qed.

  Inductive state τ :=
  | mk_state (c : expr · τ) (σ : Entropy) (k : kont τ)
  .
  Arguments mk_state {τ} c σ k.

  Definition exstate := {τ : Ty & state τ}.
  Definition mk_exstate {τ} c σ k :=
    existT _ τ (mk_state c σ k).

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

  Lemma discriminate_option {A} {x : A} : (~ None = Some x).
  Proof.
    discriminate.
  Qed.

  Reserved Infix "-->" (at level 84).
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

  Lemma decide_val {τ} (e : expr · τ) :
    {is_val e} + {~ is_val e}.
  Proof.
    destruct e; cbn; solve [left; auto | right; auto].
  Qed.

  Lemma step_deterministic τ (s : state τ) :
    {s'w : exstate ⨉ R+ &
           let (s', w) := s'w in
           (s --> projT2 s') w ⨉
           forall s'' w', (s --> projT2 s'') w' -> s' = s'' /\ w = w'
    } +
    ({s'w : exstate ⨉ R+ &
            let (s', w) := s'w in
            (s --> projT2 s') w} -> False).
  Proof.
    destruct s.
    destruct (decide_val c). {
      destruct k using kont_rect'. {
        right.
        intros [[[τ' s'] w] H].
        cbn in H.
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

        eexists (mk_exstate _ _ _, _) ; repeat constructor; [| inversion H; auto; fail].
        destruct s'' as [τ' s''].
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

        eexists (mk_exstate _ _ _, _); repeat constructor; [| inversion H; auto; fail].
        destruct s'' as [τ' s''].
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

          eexists (mk_exstate _ _ _, finite r r0); repeat constructor; [| inversion H; auto; fail].
          destruct s'' as [τ' s''].
          cbn in *.
          d_destruct H.
          auto.
        } {
          right.

          intros [[[τ' s'] w] H].
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

        eexists (mk_exstate _ _ _, _); repeat constructor; [| inversion H; auto; fail].
        destruct s'' as [τ' s''].
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

        eexists (mk_exstate _ _ _, _); repeat constructor; [| inversion H; auto; fail].
        destruct s'' as [τ' s''].
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
        eexists (mk_exstate _ _ _, _); repeat constructor; [| inversion H; auto; fail].
        destruct s'' as [τ' s''].
        cbn in *.

        d_destruct H; try absurd_val.
        auto.
      } {
        eexists (mk_exstate _ _ _, _); repeat constructor; [| inversion H; auto; fail].
        destruct s'' as [τ' s''].
        cbn in *.

        d_destruct H; try absurd_val.
        auto.
      } {
        eexists (mk_exstate _ _ _, _); repeat constructor; [| inversion H; auto; fail].
        destruct s'' as [τ' s''].
        cbn in *.

        d_destruct H; try absurd_val.
        auto.
      } {
        eexists (mk_exstate _ _ _, _); repeat constructor; [| inversion H; auto; fail].
        destruct s'' as [τ' s''].
        cbn in *.

        d_destruct H; try absurd_val.
        auto.
      }
    }
  Qed.

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
  (* Inductive step_star : forall {τ τ'}, state τ -> state τ' -> Type := *)
  (* | step_refl : forall {τ} (s : state τ), *)
  (*     s -->* s *)
  (* | step_one : forall {τ0 τ1 τ2} (s0 : state τ0) (s1 : state τ1) (s2 : state τ2), *)
  (*     s0 --> s1 -> *)
  (*     s1 -->* s2 -> *)
  (*     s0 -->* s2 *)
  (* where "s0 -->* s1" := (step_star s0 s1). *)

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
      cbn in *.
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
      replace (e_lam body) with (v_lam body : expr · (τa ~> τr)) by auto.
      rewrite <- ennr_mul_1_l.
      eapply step_one; [constructor |].

      replace w1 with (w1 * (1 * 1)) by ring.
      eapply step_star_trans; eauto.

      eapply step_one; [constructor |].
      apply step_refl.
    } {
      cbn in *.

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
      rewrite !rewrite_v_real in *.
      rewrite <- ennr_mul_1_l.
      eapply step_one; [constructor |].
      rewrite <- ennr_mul_1_r.
      eapply step_star_trans; eauto.
      rewrite <- ennr_mul_1_l.
      eapply step_one; [constructor |].
      apply step_refl.
    }
  Qed.
End AbstractMachine.

Module AbstractMachineNotations.
  Infix "-->" := (step _) (at level 84).
  Infix "-->*" := (step_star _) (at level 84).
  Notation "s -->^[ n ] t" := (step_n _ n s t) (at level 84).
End AbstractMachineNotations.
Import AbstractMachineNotations.

Definition unabstract_frame {τo τi} (eσ : expr · τi ⨉ Entropy) (f : kont_frame τi τo)
  : (expr · τo ⨉ Entropy) :=
  match f in (kont_frame τi' τo') return τi = τi' -> (expr · τo' ⨉ Entropy) with
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

(* unabstract relates AM states back to terms (with some entropy manipulation.
   This is needed to be the intermediate correspondance between big and small
   step. unabstract_rev does the same, but inducts outside-in. *)
Fixpoint unabstract_rev {τo τi} (eσ : expr · τi ⨉ Entropy) (rk : rev_kont τo τi)
  : (expr · τo ⨉ Entropy) :=
  match rk in chain _ τo' τi' return (τi = τi' -> expr · τo' ⨉ Entropy) with
  | chain_nil => fun Hτi => rew [fun ti => expr · ti ⨉ Entropy] Hτi in eσ
  | @chain_cons _ _ τo' τm τi' f rk' =>
    fun Hτi =>
      unabstract_frame (unabstract_rev eσ (rew <- Hτi in rk') : expr · τm ⨉ Entropy) f
  end eq_refl.


Check kont_frame.
Check (flip kont_frame).
Definition unabstract {τo τi} (eσ : expr · τi ⨉ Entropy) (k : kont τo τi)
  : (expr · τo ⨉ Entropy) := unabstract_rev eσ (chain_rev k).

Fixpoint unabstract' {τP τ} (eσ : expr · τ ⨉ Entropy) (k : kont τP τ)
  : (expr · τP ⨉ Entropy) :=
  match k in chain _ τ' τP'
        return τ = τ' -> (expr · τP' ⨉ Entropy) with
  | chain_nil =>
    fun Hτ =>
      (rew [fun t => expr · t ⨉ Entropy] Hτ in eσ)
  | @chain_cons _ _ τ0 τ1 τP' f k' =>
    fun Hτ =>
      unabstract' (unabstract_frame eσ (rew <-[fun t => kont_frame t τ1] Hτ in f)) k'
  end eq_refl.

Lemma unabstract_compose {τo τm τi} (eσ : expr · τi ⨉ Entropy)
      (ko : kont τo τm) (ki : kont τm τi) :
  unabstract eσ (ki +++ ko) = unabstract (unabstract eσ ki) ko.
Proof.
  induction ko using @rev_chain_rect; cbn in *; auto. {
    f_equal.
    apply chain_app_nil_r.
  } {
    specialize (IHko ki).
    unfold unabstract, chain_snoc in *.
    rewrite !chain_rev_app_distr.
    rewrite chain_rev_app_distr in IHko.
    cbn in *.
    rewrite IHko.
    auto.
  }
Qed.

Lemma unabstract'_compose {τo τm τi} (eσ : expr · τi ⨉ Entropy)
      (ko : kont τo τm) (ki : kont τm τi) :
  unabstract' (unabstract' eσ ki) ko = unabstract' eσ (ki +++ ko).
Proof.
  revert eσ.
  induction ki; cbn; auto.
Qed.

Lemma unabstracts_eq {τo τi} eσ (k : kont τo τi) : unabstract eσ k = unabstract' eσ k.
Proof.
  revert eσ.
  induction k; intros; auto.

  replace (p ::: k) with ((p ::: chain_nil) +++ k) by auto.

  pose proof unabstract_compose eσ k (p ::: chain_nil).
  pose proof unabstract'_compose eσ k (p ::: chain_nil).
  cbn in *.
  rewrite H.
  apply IHk.
Qed.

(* just like kont_rect', but inducts over τP inwards instead of τ outwards *)
Lemma
  kont_rect_rev {τ} (P : forall τP : Ty, kont τP τ -> Type)
  (case_halt : P τ (kHalt _))
  (case_app_fn :
     forall (τa τr : Ty) (σ : Entropy) (ea : expr · τa) (k : kont (τa ~> τr) τ),
       P (τa ~> τr) k -> P τr (chain_snoc k (kAppFn σ ea)))
  (case_app_arg :
     forall (τa τr : Ty) (σ : Entropy) (vf : val (τa ~> τr)) (k : kont τa τ),
       P τa k -> P τr (chain_snoc k (kAppArg σ vf)))
  (case_factor :
     forall k : kont ℝ τ,
       P ℝ k -> P ℝ (chain_snoc k kFactor))
  (case_plus_l :
     forall (σ : Entropy) (er : expr · ℝ) (k : kont ℝ τ),
       P ℝ k -> P ℝ (chain_snoc k (kPlusL σ er)))
  (case_plus_r :
     forall (vl : val ℝ) (k : kont ℝ τ),
       P ℝ k -> P ℝ (chain_snoc k (kPlusR vl)))
  : forall τP k, P τP k.
Proof.
  intros.
  induction k using @rev_chain_rect. {
    apply case_halt.
  } {
    specialize (IHk P case_halt case_app_fn case_app_arg case_factor case_plus_l case_plus_r).
    destruct x; auto.
  }
Qed.

Arguments mk_state {τP τ} c σ k.

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

Lemma extend_kont_step {τ τ' τP τP'} (e : expr · τ) (e' : expr · τ')
      (σ σ' : Entropy)
      (w : R+)
      (k : kont τP τ) (k' : kont τP τ') (k'' : kont τP' τP) :
  (mk_state e σ k --> mk_state e' σ' k') w ->
  (mk_state e σ (chain_app k k'')  --> mk_state e' σ' (chain_app k' k'')) w.
Proof.
  intros.
  d_destruct H; constructor.
Qed.

Lemma extend_kont_step_star {τ τ' τP τP'} (e : expr · τ) (e' : expr · τ')
      (σ σ' : Entropy)
      (w : R+)
      (k : kont τP τ) (k' : kont τP τ') (k'' : kont τP' τP)
      (n : nat) :
  (mk_state e σ k -->^[n] mk_state e' σ' k') w ->
  (mk_state e σ (chain_app k k'') -->^[n] mk_state e' σ' (chain_app k' k'')) w.
Proof.
  intros.
  dependent induction H. {
    constructor.
  } {
    destruct s1.
    econstructor; eauto.
    apply extend_kont_step; auto.
  }
Qed.

(* Lemma unabstract_val {τP τ σ} {v : val τ} {k : kont τP τ} : *)
(*   is_val (fst (unabstract (v : expr · τ, σ) k)) -> *)
(*   k ~= kHalt τP. *)
(* Proof. *)
(*   intros. *)
(*   induction k using @rev_chain_rect. { *)
(*     auto. *)
(*   } { *)
(*     exfalso. *)
(*     cbn in *. *)
(*     unfold chain_snoc, unabstract in *. *)
(*     rewrite chain_rev_app_distr in H. *)
(*     destruct x; cbn in *. destruct unabstract_rev; contradiction H. *)
(*   } *)
(* Qed. *)

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

Lemma irrelevance_of_unabstract_val_entropy
      {τP τ} (vf : val τ) {σ σ'} {k : kont τP τ}
      eP σP e'P σ'P :
  (eP, σP) = unabstract (vf : expr · τ, σ) k ->
  (e'P, σ'P) = unabstract (vf : expr · τ, σ') k ->
  forall v w,
    (EVAL σP ⊢ eP ⇓ v, w) ->
    (EVAL σ'P ⊢ e'P ⇓ v, w).
Proof.
  revert σP σ'P.
  induction k using @rev_chain_rect; cbn; intros. {
    inject H.
    inject H0.
    destruct (invert_eval_val H1); subst.
    constructor.
  } {
    specialize (IHk vf).
    unfold chain_snoc in *.
    rewrite unabstract_compose in H, H0.
    cbn in *.

    remember (unabstract (_, σ) _).
    remember (unabstract (_, σ') _).
    destruct p as [eP' σP'], p0 as [e'P' σ'P'].

    specialize (IHk _ _ _ _ eq_refl eq_refl).

    destruct x; cbn in *; inject H; inject H0; intros. {
      d_destruct H1; try absurd_val.
      econstructor; π_join; eauto.
    } {
      d_destruct H1; try absurd_val.
      destruct (invert_eval_val H1_); subst.
      econstructor; π_join; eauto.
    } {
      d_destruct H1; try absurd_val.
      econstructor; eauto.
    } {
      d_destruct H1; try absurd_val.
      econstructor; π_join; eauto.
    } {
      d_destruct H1; try absurd_val.
      destruct (invert_eval_val H1_); subst.
      econstructor; π_join; eauto.
    }
  }
Qed.

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
  dependent induction k' using @rev_chain_rect. {
    cbn in *.
    autoinjections.
    auto.
  } {
    unfold chain_snoc in *.
    rewrite unabstract_compose in Heqp, Heqp0.
    cbn in *.

    specialize (IHk' e e').

    d_destruct x;
      cbn in *;
      inject Heqp;
      inject Heqp0;
      remember (unabstract (e, _) _) in *;
      remember (unabstract (e', _) _) in *;
      destruct p as [eP σP], p0 as [e'P σ'P];
      cbn in *;
      specialize (IHk' _ _ eq_refl _ _ eq_refl);
      d_destruct HP; try absurd_val.
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

  d_destruct H;
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
    d_destruct H; try absurd_val.
    destruct (invert_eval_val H); subst.
    repeat econstructor; π_join; eauto.
  } {
    replace w with (1 * 1 * w) by ring.
    rewrite rewrite_v_lam.
    repeat econstructor; π_join; eauto.
  } {
    econstructor; eauto.
  } {
    d_destruct H; try absurd_val.
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
    d_destruct s.
    constructor.
  } {
    d_destruct s.
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
  auto.
Qed.

Lemma big_implies_small {τ} (σ : Entropy) (e : expr · τ) (v : val τ) (w : R+) :
  (EVAL σ ⊢ e ⇓ v, w) ->
  evals_to σ e v w.
Proof.
  intros.
  apply big_implies_small'.
  auto.
Qed.