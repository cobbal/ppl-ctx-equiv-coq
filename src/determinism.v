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

  Inductive E_rel'_eval τ ϕ {V_rel_τ : rel (val τ)} (e : expr · τ ϕ) σ : Type :=
  | eval_ex_unique
      (v : val τ) (w : R+)
      (Hv : V_rel_τ v)
      (Heval : (EVAL σ ⊢ e ⇓ v, w))
      (Hu : forall v' w', (EVAL σ ⊢ e ⇓ v', w' -> v' = v /\ w' = w))
  | eval_not_ex
      (H : {vw : (val τ * R+) &
                 let (v, w) := vw in
                 EVAL σ ⊢ e ⇓ v, w} -> False).
  Arguments eval_ex_unique {τ ϕ V_rel_τ e σ} v w Hv Heval Hu.
  Arguments eval_not_ex {τ ϕ V_rel_τ e σ} H.

  (* Note: this type is only inhabited when τ = ℝ and ϕ = ObsR *)
  Inductive E_rel'_obs_eval σ (v : val ℝ) : forall {ϕ τ} (e : expr · τ ϕ), Type :=
  | oeval_ex_unique
      e
      (w : R+)
      (Heval : OBS_EVAL σ ⊢ e ⇓ v, w)
      (Hu : forall w', (OBS_EVAL σ ⊢ e ⇓ v, w' -> w' = w)) :
      E_rel'_obs_eval σ v e
  | oeval_not_ex
      e
      (H : {w : R+ & OBS_EVAL σ ⊢ e ⇓ v, w} -> False) :
      E_rel'_obs_eval σ v e.
  Arguments oeval_ex_unique {σ v e} w Heval Hu.
  Arguments oeval_not_ex {σ v e} H.

  (* well this is clear... *)
  Definition E_rel' τ ϕ {V_rel_τ : rel (val τ)} : rel (expr · τ ϕ) :=
    fun e => forall σ,
        @E_rel'_eval τ ϕ V_rel_τ e σ ⨉
                     forall (Hτ : τ = ℝ) (Hϕ : ϕ = ObsR) (v : val ℝ),
                       E_rel'_obs_eval σ v e.
End DeterminismBase.

Module DeterminismCases : CASES DeterminismBase.
  Module Defs := Defs DeterminismBase.
  Export Defs.

  Lemma case_val : forall τ v,
      V_rel τ v -> E_rel τ _ v.
  Proof.
    split; intros; try discriminate.
    apply (eval_ex_unique v 1); auto. {
      constructor.
    } {
      intros.
      destruct (invert_eval_val H); auto.
    }
  Qed.

  Lemma case_real : forall r,
      E_rel ℝ _ (e_real r).
  Proof.
    split; intros; try discriminate.
    rewrite rewrite_v_real.
    apply case_val.
    exact I.
  Qed.

  Lemma case_lam : forall τa ϕ τr body,
      (forall v,
          V_rel τa v ->
          E_rel τr _ (proj1_sig (ty_subst1 body v))) ->
      E_rel (τa ~~ ϕ ~> τr) _ (e_lam body).
  Proof.
    split; intros; try discriminate.
    rewrite rewrite_v_lam.
    apply case_val.
    constructor; auto.
  Qed.

  Lemma case_app : forall τa ϕ τr ϕf ϕa ef ea,
      E_rel (τa ~~ ϕ ~> τr) ϕf ef ->
      E_rel τa ϕa ea ->
      E_rel τr _ (e_app ef ea).
  Proof.
    repeat intro.
    specialize (X (π 0 σ)).
    specialize (X0 (π 1 σ)).
    destruct X, X0.

    destruct e as [vf wf Hf Ef uf | not_ex]. {
      destruct e1 as [va wa Ha Ea ua | not_ex]. {
        destruct Hf as [body Hbody].
        specialize (Hbody va Ha (π 2 σ)).
        split. {
          destruct Hbody as [[vr wr Hr Er ur | not_ex] _]. {
            eapply (eval_ex_unique vr (wf * wa * wr)); auto. {
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
          intros.
          subst.
          cbn in *.
          destruct Hbody as [_ Hbody].
          specialize (Hbody eq_refl eq_refl v).
          d_destruct Hbody. {
            apply (oeval_ex_unique (wf * wa * w)). {
              econstructor; eauto.
            } {
              intros.
              d_destruct H; try absurd_val.
              specialize (uf _ _ e).
              specialize (ua _ _ e1).
              inject ua.
              inject uf.
              d_destruct H0.
              elim_sig_exprs.
              elim_erase_eqs.
              specialize (Hu _ H).
              inject Hu.
              auto.
            }
          } {
            right.
            contradict H.
            destruct H as [w E].
            d_destruct E; try absurd_val.

            specialize (uf _ _ e).
            inject uf.
            d_destruct H.

            specialize (ua _ _ e1).
            inject ua.

            eexists; eauto.
          }
        }
      } {
        split;
          intros;
          subst;
          right;
          contradict not_ex.
        {
          destruct not_ex as [[v w] E].
          d_destruct E; try absurd_val.
          eexists (_, _); eauto.
        } {
          destruct not_ex as [w E].
          d_destruct E; try absurd_val.
          eexists (_, _); eauto.
        }
      }
    } {
      split;
        intros;
        subst;
        right;
        contradict not_ex.
      {
        destruct not_ex as [[v w] E].
        d_destruct E; try absurd_val.
        eexists (_, _); eauto.
      } {
        destruct not_ex as [w E].
        d_destruct E; try absurd_val.
        eexists (_, _); eauto.
      }
    }
  Qed.

  Lemma case_factor :
    forall ϕ e,
      E_rel ℝ ϕ e ->
      E_rel ℝ _ (e_factor e).
  Proof.
    repeat intro.
    split; intros; [| discriminate].
    specialize (X σ).
    destruct X as [[v w H E u | not_ex] _]. {
      destruct_val v.
      destruct (Rle_dec 0 r). {
        apply (eval_ex_unique (v_real r) (finite r r0 * w)); auto. {
          exact (EFactor σ r0 E).
        } {
          intros.
          d_destruct H0; try absurd_val.
          specialize (u _ _ H0).
          inject u.
          inject H1.
          split; auto.
          f_equal.
          ennr.
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
    E_rel ℝ _ e_sample.
  Proof.
    repeat intro.
    split. {
      eapply (eval_ex_unique _ 1);
        try constructor;
        d_destruct H;
        auto.
    } {
      intros.
      clear Hτ Hϕ.

      destruct_val v.
      assert ({0 <= r <= 1} + {~ 0 <= r <= 1}). {
        destruct (Rle_dec 0 r); [| right; tauto].
        destruct (Rle_dec r 1); [left | right]; tauto.
      }
      destruct H. {
        apply (oeval_ex_unique 1). {
          constructor.
          auto.
        } {
          intros.
          d_destruct H.
          auto.
        }
      } {
        right.
        contradict n.
        destruct n.
        d_destruct e.
        auto.
      }
    }
  Qed.

  Lemma case_observe : forall ϕ0 e0 e1,
      E_rel ℝ ϕ0 e0 ->
      E_rel ℝ _ e1 ->
      E_rel ℝ _ (e_observe e0 e1).
  Proof.
    repeat intro.
    split; intros; try discriminate.
    specialize (X (π 0 σ)).
    specialize (X0 (π 1 σ)).

    destruct X as [[vl wl Hl El ul | not_ex] _]. {
      destruct X0 as [_ X0].
      specialize (X0 eq_refl eq_refl vl).
      d_destruct X0. {
        apply (eval_ex_unique vl (wl * w)); auto. {
          constructor; auto.
        } {
          intros.
          d_destruct H; try absurd_val.
          specialize (ul _ _ H).
          inject ul.
          specialize (Hu _ e).
          inject Hu.
          auto.
        }
      } {
        right.
        contradict H.

        destruct H as [[v w] ?].
        d_destruct y; try absurd_val.
        specialize (ul _ _ y).
        inject ul.
        eexists; eauto.
      }
    } {
      right.
      clear X0.
      contradict not_ex.
      destruct not_ex as [[v w] ?].
      d_destruct y; try absurd_val.
      eexists (_, _); eauto.
    }
  Qed.

  Lemma case_unop : forall ϕ op e,
      E_rel ℝ ϕ e ->
      E_rel ℝ _ (e_unop op e).
  Proof.
    repeat intro.
    specialize (X σ).

    split. {
      destruct X as [[v w Hv E u | not_ex] _]. {
        destruct_val v.
        remember (δ1 op r).
        destruct o. {
          apply (eval_ex_unique (v_real r0) w); auto. {
            econstructor; eauto.
          } {
            intros.
            d_destruct H; try absurd_val.
            destruct (u _ _ H); subst.
            inject H0.
            rewrite <- Heqo in e1.
            inject e1.
            auto.
          }
        } {
          right.
          intros.
          destruct X as [[v' w'] E'].
          d_destruct E'; try absurd_val.
          specialize (u _ _ E').
          destruct u.
          inject H.
          rewrite <- Heqo in e1.
          discriminate e1.
        }
      } {
        eapply eval_not_ex. {
          intros [[v w] E].
          d_destruct E; try absurd_val.
          destruct is_v0.
          contradict not_ex.
          eexists (_, _); eauto.
        }
      }
    } {
      destruct X as [_ X].
      intros.
      subst.
      d_destruct Hτ.
      specialize (X eq_refl eq_refl).
      cbn in *.

      destruct_val v.

      remember (δ1_inv op r) as rr.
      destruct rr as [rr |]. {
        specialize (X (v_real rr)).
        d_destruct X. {
          eapply oeval_ex_unique. {
            econstructor; eauto.
          } {
            intros.

            d_destruct H; try absurd_val.
            rewrite <- Heqrr in e1.
            inject e1.
            destruct is_v0.

            destruct (Hu _ H).
            reflexivity.
          }
        } {
          apply oeval_not_ex.
          intros [w' E'].
          contradict H.
          d_destruct E'.
          destruct is_v0.
          rewrite <- Heqrr in e1.
          inject e1.
          eauto.
        }
      } {
        eapply oeval_not_ex. {
          intros [w' E'].
          d_destruct E'.
          rewrite <- Heqrr in e1.
          discriminate e1.
        }
      }
    }
  Qed.

  Lemma case_binop : forall ϕl ϕr ϕ op Hϕ el er,
      E_rel ℝ ϕl el ->
      E_rel ℝ ϕr er ->
      E_rel ℝ ϕ (e_binop op Hϕ el er).
  Proof.
    repeat intro.
    specialize (X (π 0 σ)).
    specialize (X0 (π 1 σ)).

    destruct X as [[vl wl Hvl EVAL_l ul | not_ex] _]. {
      split. {
        destruct X0 as [[vr wr Hvr EVAL_r ur | not_ex] _]. {
          destruct_val vl.
          destruct_val vr.

          remember (δ2 op r r0).
          destruct o. {
            apply (eval_ex_unique (v_real r1) (wl * wr)); auto. {
              econstructor; eauto.
            } {
              intros.

              d_destruct H; try absurd_val.

              destruct (ul _ _ H); subst.
              destruct (ur _ _ H0); subst.
              inject H1.
              inject H2.
              rewrite <- Heqo in e.
              inject e.
              auto.
            }
          } {
            apply eval_not_ex.
            intros [[v w] E].
            d_destruct E; try absurd_val.

            destruct (ul _ _ E1).
            destruct (ur _ _ E2).
            inject H.
            inject H1.

            rewrite <- Heqo in e.
            discriminate e.
          }
        } {
          right.
          contradict not_ex.
          destruct not_ex as [[v w] E].
          d_destruct E; try absurd_val.
          eexists (_, _); eauto.
        }
      } {
        intros.
        subst.
        destruct X0 as [_ X0].
        destruct_val vl.
        destruct_val v.
        assert (ϕr = ObsR). {
          destruct ϕr; auto.
          destruct op; discriminate Hϕ0.
        }
        subst ϕr.
        assert (binop_effect op = ObsR). {
          setoid_rewrite effect_compose_id_r in Hϕ0.
          auto.
        }

        enough (E_rel'_obs_eval σ (v_real r0) (rew Hϕ0 in (e_binop op eq_refl el er))). {
          d_destruct Hϕ0.
          exact H0.
        }

        d_destruct Hτ.
        remember (δ2_inv op r r0) as rr.
        destruct rr as [rr |]. {
          intros.
          pose proof (δ2_inv_sound (eq_sym Heqrr)).

          specialize (X0 eq_refl eq_refl (v_real rr)).
          cbn in *.
          d_destruct X0. {
            eapply oeval_ex_unique. {
              destruct op; cbn in Hϕ0; d_destruct Hϕ0;
                econstructor; eauto.
            } {
              intros.
              generalize_refl (δϕ2 op ObsR).
              subst.
              cbn in *.
              d_destruct H1.
              destruct is_v0, is_v1.

              specialize (ul _ _ e).
              d_destruct ul.
              d_destruct H.
              subst.

              rewrite <- Heqrr in e2.
              inject e2.

              specialize (Hu _ H3).
              subst.
              auto.
            }
          } {
            right.
            contradict H.
            destruct H as [w H].
            generalize_refl (δϕ2 op ObsR); subst; cbn in *.
            d_destruct H.
            destruct is_v0, is_v1.

            specialize (ul _ _ e).
            d_destruct ul.
            d_destruct H.
            subst.

            rewrite <- Heqrr in e2.
            inject e2.

            eexists; eauto.
          }
        } {
          right.
          destruct op; d_destruct Heqrr.
          intros [w H0].
          d_destruct (Hϕ0, H0).
          destruct is_v0, is_v1.

          specialize (ul _ _ e).
          d_destruct ul.
          d_destruct H.
          subst.
          rewrite e2 in *.
          discriminate.
        }
      }
    } {
      split. {
        right.
        contradict not_ex.
        destruct not_ex as [[v w] E].
        d_destruct E; try absurd_val.
        eexists (_, _); eauto.
      } {
        intros.
        enough (E_rel'_obs_eval σ v (rew Hϕ0 in (e_binop op Hϕ el er))). {
          d_destruct Hϕ0.
          exact H.
        }
        right.
        contradict not_ex.
        destruct not_ex as [w E].
        subst.
        generalize_refl (δϕ2 op ϕr); subst; cbn in *.
        d_destruct E; try absurd_val.
        eexists (_, _); eauto.
      }
    }
  Qed.

  Lemma case_hide : forall e,
      E_rel ℝ ObsR e ->
      E_rel ℝ ObsNone (e_hide_observable e).
  Proof.
    repeat intro.

    specialize (X σ).
    split. {
      destruct X as [[vl wl Hvl EVAL_l ul | not_ex] _]. {
        eapply eval_ex_unique; try solve [constructor; eauto].
        intros.
        d_destruct H; try absurd_val.
        apply ul.
        assumption.
      } {
        right.
        contradict not_ex.
        destruct not_ex as [[v w] E].
        d_destruct E; try absurd_val.
        eexists (_, _); eauto.
      }
    } {
      intros.
      discriminate.
    }
  Qed.

End DeterminismCases.

Module Determinism := Compatibility DeterminismBase DeterminismCases.
Export Determinism.

Inductive eval_dec_result {τ ϕ} (e : expr · τ ϕ) (σ : Entropy) :=
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
Arguments eval_dec_ex_unique {_ _ _ _} v w _ _.
Arguments eval_dec_not_ex {_ _ _ _} not_ex.

Inductive obs_eval_dec_result (e : expr · ℝ ObsR) (σ : Entropy) (v : val ℝ) :=
| obs_eval_dec_ex_unique
    (w : R+) (ev : OBS_EVAL σ ⊢ e ⇓ v, w)
    (u : forall w', (OBS_EVAL σ ⊢ e ⇓ v, w') -> w' = w)
| obs_eval_dec_not_ex
    (not_ex : forall w, (OBS_EVAL σ ⊢ e ⇓ v, w) -> False)
.
Arguments obs_eval_dec_ex_unique {_ _ _} w _ _.
Arguments obs_eval_dec_not_ex {_ _ _} not_ex.

Theorem eval_dec {τ ϕ} (e : expr · τ ϕ) σ : eval_dec_result e σ.
Proof.
  destruct (fundamental_property e dep_nil I σ) as [fp _].

  elim_sig_exprs.
  elim_erase_eqs.

  destruct fp. {
    eapply eval_dec_ex_unique; eauto.
  } {
    apply eval_dec_not_ex.
    intros.
    contradict H.
    exists (v, w).
    auto.
  }
Qed.

Theorem obs_eval_dec e σ v : obs_eval_dec_result e σ v.
Proof.
  destruct (fundamental_property e dep_nil I σ) as [_ fp].
  specialize (fp eq_refl eq_refl v).

  elim_sig_exprs.
  elim_erase_eqs.

  d_destruct fp. {
    eapply obs_eval_dec_ex_unique; eauto.
  } {
    apply obs_eval_dec_not_ex.
    intros.
    contradict H.
    exists w.
    auto.
  }
Qed.