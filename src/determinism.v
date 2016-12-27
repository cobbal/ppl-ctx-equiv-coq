Require Import Reals.
Require Import List.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import Coq.fourier.Fourier.
Require Import nnr.
Require Import syntax.
Require Import utils.
Require Import micromega.Lia.
Require Import logrel.

Import EqNotations.

Local Open Scope ennr.

Import Log_rel1.
Module DeterminismBase <: BASE.

  Definition V_rel_real : rel (val ℝ) :=
    fun v => True.

  Definition E_rel' τ (V_rel_τ : rel (val τ)) : rel (expr · τ) :=
    fun e =>
      forall σ,
        {vw : (val τ * R+) &
              let (v, w) := vw in
              (V_rel_τ v)
                ⨉ (EVAL σ ⊢ e ⇓ v, w)
                ⨉ (forall v' w', (EVAL σ ⊢ e ⇓ v', w') -> v' = v /\ w' = w)
        } +
        ({vw : (val τ * R+) &
               let (v, w) := vw in EVAL σ ⊢ e ⇓ v, w}
         -> False).
End DeterminismBase.

Module DeterminismCases : CASES DeterminismBase.
  Module Defs := Defs DeterminismBase.
  Export Defs.

  Lemma case_val : forall τ v,
      V_rel τ v -> E_rel τ v.
  Proof.
    left.
    exists (v, 1).

    split; [split|]; auto. {
      constructor.
    } {
      intros.
      destruct (invert_eval_val H); auto.
    }
  Qed.

  Lemma case_real : forall r,
      E_rel ℝ (e_real r).
  Proof.
    intros.
    rewrite rewrite_v_real.
    apply case_val.
    exact I.
  Qed.

  Lemma case_lam : forall τa τr body,
      (forall v,
          V_rel τa v ->
          E_rel τr (proj1_sig (ty_subst1 body v))) ->
      E_rel (τa ~> τr) (e_lam body).
  Proof.
    intros.
    rewrite rewrite_v_lam.
    apply case_val.
    constructor; auto.
  Qed.

  Lemma case_app : forall τa τr ef ea,
      E_rel (τa ~> τr) ef ->
      E_rel τa ea ->
      E_rel τr (e_app ef ea).
  Proof.
    repeat intro.
    specialize (X (π 0 σ)).
    specialize (X0 (π 1 σ)).
    destruct X as [[[vf wf] [[Hf Ef] uf]] | not_ex]. {
      destruct X0 as [[[va wa] [[Ha Ea] ua]] | not_ex]. {
        destruct Hf as [body Hbody].
        specialize (Hbody va Ha (π 2 σ)).
        destruct Hbody as [[[vr wr] [[Hr Er] ur]] | not_ex]. {
          left.
          exists (vr, wf * wa * wr).
          split; [split |]; auto. {
            econstructor; eauto.
          } {
            intros.
            d_destruct H; try absurd_val.
            specialize (uf _ _ H).
            specialize (ua _ _ H0).
            inject ua.
            inject uf.
            d_destruct H0.
            elim_sig_exprs.
            elim_erase_eqs.
            specialize (ur _ _ H1).
            inject ur.
            auto.
          }
        } {
          right.
          contradict not_ex.
          destruct not_ex as [[v w] E].
          d_destruct E; try absurd_val.

          specialize (uf _ _ E1).
          inject uf.
          d_destruct H.

          specialize (ua _ _ E2).
          inject ua.

          eexists (_, _); eauto.
        }
      } {
        right.
        contradict not_ex.
        destruct not_ex as [[v w] E].
        d_destruct E; try absurd_val.
        eexists (_, _); eauto.
      }
    } {
      right.
      contradict not_ex.
      destruct not_ex as [[v w] E].
      d_destruct E; try absurd_val.
      eexists (_, _); eauto.
    }
  Qed.

  Lemma case_factor : forall e,
      E_rel ℝ e ->
      E_rel ℝ (e_factor e).
  Proof.
    repeat intro.
    specialize (X σ).
    destruct X as [[[v w] [[H E] u]] | not_ex]. {
      destruct_val v.
      destruct (Rle_dec 0 r). {
        left.
        exists (v_real r, finite r r0 * w).
        split; [split |]; auto. {
          exact (EFactor σ r0 E).
        } {
          intros.
          d_destruct H0; try absurd_val.
          specialize (u _ _ H0).
          inject u.
          inject H1.
          split; repeat f_equal.
          apply proof_irrelevance.
        }
      } {
        right.
        contradict n.
        destruct n as [[v w'] E'].
        d_destruct E'; try absurd_val.
        specialize (u _ _ E').
        inject u.
        d_destruct H0.
        auto.
      }
    } {
      right.
      contradict not_ex.
      destruct not_ex as [[v w] E].
      d_destruct E; try absurd_val.
      eexists (_, _); eauto.
    }
  Qed.

  Lemma case_sample :
    E_rel ℝ e_sample.
  Proof.
    repeat intro.
    left.
    eexists (_, _).
    split; [split |]; swap 1 2. {
      constructor.
    } {
      exact I.
    } {
      intros.
      d_destruct H; try absurd_val.
      auto.
    }
  Qed.

  Lemma case_plus : forall el er,
      E_rel ℝ el ->
      E_rel ℝ er ->
      E_rel ℝ (e_plus el er).
  Proof.
    repeat intro.
    specialize (X (π 0 σ)).
    specialize (X0 (π 1 σ)).

    destruct X as [[[vl wl] [[Hvl EVAL_l] ul]] | not_ex]. {
      destruct X0 as [[[vr wr] [[Hvr EVAL_r] ur]] | not_ex]. {
        left.
        destruct_val vl.
        destruct_val vr.

        exists (v_real (r + r0), wl * wr).
        constructor; [repeat econstructor |]; eauto.
        intros.

        d_destruct H; try absurd_val.

        destruct (ul _ _ H); subst.
        destruct (ur _ _ H0); subst.
        inject H1.
        inject H2.

        split; auto.
      } {
        right.
        intros.

        contradict not_ex.

        destruct X as [[? ?] ?].
        d_destruct y; try absurd_val.

        eexists (_, _); eauto.
      }
    } {
      right.
      intros.

      contradict not_ex.

      destruct X as [[? ?] ?].
      d_destruct y; try absurd_val.

      eexists (_, _); eauto.
    }
  Qed.
End DeterminismCases.

Module Determinism := Compatibility DeterminismBase DeterminismCases.
Export Determinism.

Inductive eval_dec_result {τ} (e : expr · τ) (σ : Entropy) :=
| eval_dec_ex_unique
    (v : val τ) (w : R+) (ev : EVAL σ ⊢ e ⇓ v, w)
    (u : forall v' w',
        (EVAL σ ⊢ e ⇓ v', w') ->
        v' = v /\ w' = w)
| eval_dec_not_ex
    (not_ex : forall v w,
        (EVAL σ ⊢ e ⇓ v, w) ->
        False)
.
Arguments eval_dec_ex_unique {_ _ _} v w _ _.
Arguments eval_dec_not_ex {_ _ _} not_ex.

Theorem eval_dec {τ} (e : expr · τ) σ : eval_dec_result e σ.
Proof.
  pose proof (fundamental_property · τ e dep_nil I) as fp.

  elim_sig_exprs.
  elim_erase_eqs.

  destruct (fp σ). {
    destruct s as [[v w] [[? ?] ?]].
    eapply eval_dec_ex_unique; eauto.
  } {
    apply eval_dec_not_ex.
    intros.
    contradict f.
    exists (v, w).
    auto.
  }
Qed.