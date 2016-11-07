Require Import Basics.
Require Import Reals.
Require Import List.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import nnr.
Require Import syntax.
Require Import utils.
Require Import Coq.Classes.Morphisms.
Require Import relations.
Require Import ctxequiv.
Require Import properties_of_relations.

Require Import micromega.Lia.

Transparent π.

Notation "x ~> y" := (Arrow x y) (at level 69, right associativity, y at level 70).
Notation "` x" := (e_var x) (at level 1).
Notation "'λ' τ , e" := (e_lam τ e) (at level 69, right associativity).
Notation "e0 @ e1" := (e_app e0 e1) (at level 68, left associativity).
Notation "e0 +! e1" := (e_plus e0 e1) (at level 68, left associativity).

Lemma πL_same_integral f :
  Integration (f ∘ πL) μEntropy = Integration f μEntropy.
Proof.
  replace (f ∘ πL) with (fun σ => block (fun σL σR => f σL) (πL σ) (πR σ)) by auto.
  rewrite integration_πL_πR.
  unfold block.
  simpl.
  f_equal.
  extensionality σ.
  erewrite int_const_entropy; eauto.
Qed.

Lemma πR_same_integral f :
  Integration (f ∘ πR) μEntropy = Integration f μEntropy.
Proof.
  replace (f ∘ πR) with (fun σ => block (fun σL σR => f σR) (πL σ) (πR σ)) by auto.
  rewrite integration_πL_πR.
  unfold block.
  simpl.
  erewrite int_const_entropy; eauto.
Qed.

Lemma project_same_integral f n :
  Integration (f ∘ π n) μEntropy = Integration f μEntropy.
Proof.
  induction n. {
    unfold π.
    apply πL_same_integral.
  } {
    rewrite <- IHn.
    clear IHn.
    replace (f ∘ π (S n)) with (f ∘ π n ∘ πR) by auto.
    apply πR_same_integral.
  }
Qed.

Lemma add_zero_related {e}
      (He : (TC · ⊢ e : ℝ)) :
  (EXP · ⊢ e_real 0 +! e ≈ e : ℝ).
Proof.
  set (left_tc := TCPlus (TCReal 0) He).
  refine (mk_related_exprs _ _ _); auto.

  simpl.
  intros ρ0 ρ1 Hρ.
  rewrite (wt_nil_unique ρ0) in *.
  rewrite (wt_nil_unique ρ1) in *.
  clear ρ0 ρ1 Hρ.

  unfold subst_of_WT_Env; simpl.
  rewrite subst_id.
  exists left_tc He.
  intros A0 A1 HA.

  subst left_tc.
  unfold μ.
  rewrite by_μe_eq_μEntropy_plus.
  rewrite (pure_is_dirac (TCReal 0) I).
  rewrite meas_id_left.
  rewrite μe_eq_μEntropy.
  integrand_extensionality σ.
  simpl.
  unfold eval_in.
  repeat f_equal.
  extensionality v.
  destruct_WT_Val v.
  unfold plus_in, Indicator.
  simpl.
  replace (0 + r)%R with r by ring.
  f_equal.
  apply HA.
  reflexivity.
Qed.

(* A subset of things that can be tonellied *)
(* TODO: figure out exactly what's needed to make this not a whitelist *)
Inductive tonelliable : forall {A}, Meas A -> Type :=
| tonelliable_μ {τ e} (He : (TC · ⊢ e : τ)) : tonelliable (μ He)
| tonelliable_sig_fi {A} (m : Meas A) : SigmaFinite m -> tonelliable m
.
Hint Constructors tonelliable.

Lemma tonelli_μ {τ0 τ1 e0 e1 B}
      (He0 : (TC · ⊢ e0 : τ0))
      (He1 : (TC · ⊢ e1 : τ1))
      (f : WT_Val τ0 -> WT_Val τ1 -> Meas B) :
  μ He0 >>= (fun x => μ He1 >>= (fun y => f x y)) =
  μ He1 >>= (fun y => μ He0 >>= (fun x => f x y)).
Proof.
Abort.

Lemma tonelli_μ_and_finite {τ B C}
      (μFin : Meas B)
      (f : WT_Val τ -> B -> Meas C)
      {e}
      (He : (TC · ⊢ e : τ)) :
  SigmaFinite μFin ->
  μ He >>= (fun x => μFin >>= (fun y => f x y)) =
  μFin >>= (fun y => μ He >>= (fun x => f x y)).
Proof.
  intros.

  extensionality ev.

  rewrite μe_eq_μEntropy.
  setoid_rewrite μe_eq_μEntropy.
  setoid_rewrite tonelli_3; auto.
  integrand_extensionality σ0.
  decide_eval as [v0 w0 ex0 u0]. {
    simpl.
    apply Integration_linear_mult_r.
  } {
    simpl.
    rewrite <- Integration_linear_mult_r.
    nnr.
  }
Qed.

Lemma tonelli
      {A B C} (μ0 : Meas A) (μ1 : Meas B)
      (f : A -> B -> Meas C) :
  tonelliable μ0 ->
  tonelliable μ1 ->
  μ0 >>= (fun x0 => μ1 >>= (fun x1 => f x0 x1)) =
  μ1 >>= (fun x1 => μ0 >>= (fun x0 => f x0 x1)).
Proof.
  intros.
  dependent destruction X;
    dependent destruction X0.
  {
    extensionality ev.

    rewrite !μe_eq_μEntropy2.
    setoid_rewrite tonelli_3 at 1; auto.
    integrand_extensionality σ0.
    integrand_extensionality σ1.

    decide_eval as [v0 w0 ex0 u0].
    decide_eval as [v1 w1 ex1 u1].
    nnr.
  } {
    rewrite tonelli_μ_and_finite; auto.
  } {
    rewrite tonelli_μ_and_finite; auto.
  } {
    extensionality ev.
    apply tonelli_3; auto.
  }
Qed.

Lemma add_comm_related Γ e1 e2 :
  (TC Γ ⊢ e1 : ℝ) ->
  (TC Γ ⊢ e2 : ℝ) ->
  (EXP Γ ⊢ e1 +! e2 ≈ e2 +! e1 : ℝ).
Proof.
  intros He1 He2.

  simple refine (relate_exprs (TCPlus _ _) (TCPlus _ _) _); auto.
  intros.

  unfold μ.

  do 2 set (close ρ _).
  clearbody t t0.
  dependent destruction t.
  replace t0 with (TCPlus t2 t1) by apply tc_unique.

  simpl. (* implicits *)
  rewrite !by_μe_eq_μEntropy_plus.
  rewrite tonelli; auto.
  integrand_extensionality v2.
  integrand_extensionality v1.

  destruct_WT_Val v1.
  destruct_WT_Val v2.
  unfold plus_in, Indicator; simpl.
  replace (r + r0)%R with (r0 + r)%R by ring.
  auto.
Qed.

(* Definition ex_left e1 e2 := (λ ℝ, e1.[ren S] +! `O) @ e2. *)
(* Definition ex_right e1 e2 := e1 +! e2. *)

(* Lemma tc_left {Γ e1 e2} *)
(*       (He1 : TC Γ ⊢ e1 : ℝ) *)
(*       (He2 : TC Γ ⊢ e2 : ℝ) : *)
(*   (TC Γ ⊢ ex_left e1 e2 : ℝ). *)
(* Proof. *)
(*   assert (TC (extend Γ ℝ) ⊢ e1.[ren S] : ℝ). { *)
(*     apply (ty_ren He1). *)
(*     auto. *)
(*   } *)
(*   repeat econstructor; eauto. *)
(* Qed. *)

(* Lemma tc_right {Γ e1 e2} *)
(*       (He1 : TC Γ ⊢ e1 : ℝ) *)
(*       (He2 : TC Γ ⊢ e2 : ℝ) : *)
(*   (TC Γ ⊢ ex_right e1 e2 : ℝ). *)
(* Proof. *)
(*   repeat constructor; auto. *)
(* Qed. *)

(* Lemma break_right {Γ e1 e2} *)
(*       (ρ : WT_Env Γ) *)
(*       (σ0 σ1 σr : Entropy) *)
(*       (He1 : (TC Γ ⊢ e1 : ℝ)) *)
(*       (He2 : (TC Γ ⊢ e2 : ℝ)) *)
(*       A : *)
(*   eval_in (close ρ (tc_right He1 He2)) A (join σ0 (join σ1 σr)) = *)
(*   option0 (plus_in A <$> ev (close ρ He1) σ0 <*> ev (close ρ He2) σ1) *)
(*           [*] ew (close ρ He1) σ0 *)
(*           [*] ew (close ρ He2) σ1. *)
(* Proof. *)
(*   intros. *)
(*   unfold eval_in. *)
(*   decide_eval as [v0 w0 ex0 u0]. { *)
(*     destruct_WT_Val v0. *)
(*     inversion ex0; subst; try absurd_Val. *)
(*     unfold π in *. *)
(*     repeat rewrite πR_join in *. *)
(*     rewrite πL_join in *. *)
(*     simpl. *)

(*     decide_eval as [v3 w3 ex3 u3]. *)
(*     destruct_WT_Val v3. *)
(*     decide_eval as [v5 w5 ex5 u5]. *)
(*     destruct_WT_Val v5. *)

(*     rewrite <- nnr_mult_assoc. *)

(*     unfold plus_in. *)
(*     simpl in *. *)

(*     destruct is_v0, is_v1. *)

(*     specialize (u3 (_, _) X). *)
(*     specialize (u5 (_, _) X0). *)
(*     inversion u3. *)
(*     inversion u5. *)
(*     subst. *)
(*     auto. *)
(*   } { *)
(*     simpl. *)
(*     decide_eval as [v3 w3 ex3 u3]. *)
(*     destruct_WT_Val v3. *)
(*     decide_eval as [v4 w4 ex4 u4]. *)
(*     destruct_WT_Val v4. *)
(*     contradict not_ex. *)

(*     eexists (v_real (r + r0) : Val, w3 [*] w4). *)

(*     econstructor; eauto. { *)
(*       unfold π. *)
(*       rewrite πL_join. *)
(*       eauto. *)
(*     } { *)
(*       unfold π. *)
(*       rewrite πR_join. *)
(*       rewrite πL_join. *)
(*       eauto. *)
(*     } *)
(*   } *)
(* Qed. *)

(* Lemma break_left {Γ e1 e2} *)
(*       (ρ : WT_Env Γ) *)
(*       (He1 : (TC Γ ⊢ e1 : ℝ)) *)
(*       (He2 : (TC Γ ⊢ e2 : ℝ)) *)
(*       σ A : *)
(*   let σe1 := (π 0 (π 2 σ)) in *)
(*   let σe2 := (π 1 σ) in *)
(*   eval_in (close ρ (tc_left He1 He2)) A σ = *)
(*   option0 (plus_in A <$> ev (close ρ He1) σe1 <*> ev (close ρ He2) σe2) *)
(*           [*] ew (close ρ He1) σe1 *)
(*           [*] ew (close ρ He2) σe2. *)
(* Proof. *)
(*   intros. *)

(*   unfold eval_in. *)
(*   decide_eval (close ρ (tc_left He1 He2)) σ as [v0 w0 ex0 u0]. { *)
(*     destruct_WT_Val v0; simpl in *. *)
(*     inversion ex0; subst; try absurd_Val. *)
(*     inversion X; subst. *)
(*     inversion H0; subst. *)
(*     dependent destruction X1. *)
(*     simpl in *. *)
(*     destruct is_v0, is_v1. *)

(*     replace (e1.[ren S].[up (subst_of_WT_Env ρ)].[v1 : Expr/]) *)
(*     with e1.[subst_of_WT_Env ρ] in * *)
(*       by autosubst. *)

(*     decide_eval as [v4 w4 ex4 u4]. *)
(*     destruct_WT_Val v4. *)
(*     decide_eval  as [v5 w5 ex5 u5]. *)
(*     destruct_WT_Val v5. *)
(*     simpl in *. *)

(*     unfold plus_in, Indicator. *)
(*     simpl. *)
(*     replace (mk_WT_Val _ _) with (v_real (r0 + r1)) *)
(*       by (apply WT_Val_eq; auto). *)

(*     specialize (u4 (_, _) X1_1). *)
(*     specialize (u5 (_, _) X0). *)
(*     inversion u4. *)
(*     inversion u5. *)
(*     subst. *)

(*     inversion X1_2; subst. *)
(*     inversion H1; subst. *)
(*     nnr. *)
(*   } { *)
(*     simpl. *)
(*     decide_eval as [v4 w4 ex4 u4]. *)
(*     destruct_WT_Val v4. *)
(*     decide_eval as [v5 w5 ex5 u5]. *)
(*     destruct_WT_Val v5. *)
(*     simpl in *. *)

(*     contradict not_ex. *)
(*     eexists (v_real (r + r0) : Val, _). *)
(*     eapply EApp; eauto. { *)
(*       eapply EPure'. *)
(*       reflexivity. *)
(*     } { *)
(*       simpl. *)
(*       replace (e1.[ren S].[up (subst_of_WT_Env ρ)].[e_real r0 : Expr/]) *)
(*       with e1.[subst_of_WT_Env ρ] in * *)
(*         by autosubst. *)
(*       apply EPlus with (is_v0 := I) (is_v1 := I); eauto. *)
(*       apply EPure'. *)
(*       reflexivity. *)
(*     } *)
(*   } *)
(* Qed. *)

(* (* map (π 0 (π 2 σ)) over to (π 0 σ) *) *)
(* Definition kajigger σ := join (π 0 (π 2 σ)) (join (π 1 σ) (π 0 σ)). *)
(* Definition kajigger_n := (join' (π_n 2 ∘ π_n 0) (join' (π_n 1) (π_n 0))). *)

(* Lemma kajigger_02 σ : (π 0 (kajigger σ)) = π 0 (π 2 σ). *)
(* Proof. *)
(*   apply πL_join. *)
(* Qed. *)
(* Lemma kajigger_1 σ : (π 1 (kajigger σ) = π 1 σ). *)
(* Proof. *)
(*   unfold kajigger. *)
(*   unfold π. *)
(*   rewrite πR_join. *)
(*   rewrite πL_join. *)
(*   auto. *)
(* Qed. *)

(* Lemma kajigger_equiv : *)
(*   shuf kajigger_n = kajigger. *)
(* Proof. *)
(*   extensionality σ. *)
(*   unfold shuf, kajigger, kajigger_n, compose, join. *)
(*   repeat rewrite <- π_π_n_correspond. *)
(*   extensionality n. *)
(*   unfold compose, join'. *)
(*   destruct Nat.even; auto. *)
(*   destruct Nat.even; auto. *)
(* Qed. *)

(* Lemma kajigger_n_inj : Injective kajigger_n. *)
(* Proof. *)
(*   intros ? ? ?. *)
(*   unfold kajigger_n, join' in H. *)
(*   simpl in H. *)

(*   unfold compose, πL_n, πR_n in H. *)

(*   repeat remember (Nat.even _) in H. *)
(*   apply even_div_2_inj; *)
(* destruct b, b0, b1, b2; *)
(* try pose proof (eq_trans (eq_sym Heqb) Heqb1); *)
(* try pose proof (eq_trans (eq_sym Heqb0) Heqb2); *)
(* auto; try lia. { *)
(*     make_even_and_odd. *)
(*     fold_doubles. *)
(*     rewrite <- Div2.even_double in H; auto. *)
(*     rewrite <- Div2.odd_double in H; auto. *)
(*     rewrite <- Div2.even_double in H; auto. *)
(*     rewrite <- Div2.odd_double in H; auto. *)
(*   } { *)
(*     make_even_and_odd. *)
(*     fold_doubles. *)
(*     repeat (apply double_inj in H || apply S_inj in H). *)
(*     apply even_div_2_inj; auto. *)
(*   } *)
(* Qed. *)

(* Lemma beta_addition {Γ e1 e2} : *)
(*   (TC Γ ⊢ e1 : ℝ) -> *)
(*   (TC Γ ⊢ e2 : ℝ) -> *)
(*   (EXP Γ ⊢ ex_left e1 e2 ≈ ex_right e1 e2 : ℝ). *)
(* Proof. *)
(*   intros He1 He2. *)

(*   refine (mk_related_exprs (tc_left He1 He2) (tc_right He1 He2) _). *)
(*   intros. *)

(*   (* destruct ρ0 as [ρ0 Hρ0]. *) *)
(*   (* destruct ρ1 as [ρ1 Hρ1]. *) *)

(*   exists (close ρ0 (tc_left He1 He2)) (close ρ1 (tc_right He1 He2)). *)
(*   intros A0 A1 HA. *)

(*   unfold μ. *)

(*   symmetry. *)
(*   rewrite (int_inj_entropy _ kajigger_n_inj). *)
(*   symmetry. *)
(*   rewrite kajigger_equiv. *)

(*   setoid_rewrite break_left. *)

(*   assert (forall σ, σ = join (π 0 σ) (join (π 1 σ) (π_leftover 2 σ))). { *)
(*     intros. *)
(*     unfold π. *)
(*     rewrite 2 join_πL_πR. *)
(*     auto. *)
(*   } *)
(*   pose proof fun σ => break_right ρ1 (π 0 σ) (π 1 σ) (π_leftover 2 σ) He1 He2. *)
(*   setoid_rewrite <- H in H0. *)
(*   setoid_rewrite H0. *)
(*   clear H H0. *)

(*   unfold compose. *)
(*   setoid_rewrite kajigger_1. *)
(*   setoid_rewrite kajigger_02. *)

(*   setoid_rewrite <- (break_right ρ0 _ _ (π 0 σ)). *)
(*   setoid_rewrite <- (break_right ρ1 _ _ (π 0 x)). *)

(*   change (Integration (eval_in (close ρ0 (tc_right He1 He2)) A0 ∘ kajigger) μEntropy = *)
(*           Integration (eval_in (close ρ1 (tc_right He1 He2)) A1 ∘ kajigger) μEntropy). *)

(*   rewrite <- kajigger_equiv. *)
(*   rewrite <- 2 (int_inj_entropy _ kajigger_n_inj). *)

(*   apply related_close1; auto. *)
(* Qed. *)

(* Lemma the_whole_enchilada {Γ e1 e2} {He1 : TC Γ ⊢ e1 : ℝ} {He2 : TC Γ ⊢ e2 : ℝ} : *)
(*   ctx_equiv (tc_left He1 He2) (tc_right He1 He2). *)
(* Proof. *)
(*   apply relation_sound. *)
(*   apply beta_addition; auto. *)
(* Qed. *)

(* Print Assumptions the_whole_enchilada. *)

Lemma pure_subst {Γ} (ρ : WT_Env Γ) x :
  is_pure `x.[subst_of_WT_Env ρ].
Proof.
  unfold subst_of_WT_Env, downgrade_env.
  simpl.
  revert x.
  destruct ρ as [ρ Hρ].
  induction Hρ; intros; simpl; auto.
  destruct x; simpl; auto.
  destruct v as [a Ha].
  destruct a; try contradiction Ha; auto.
Qed.

Lemma beta_value {Γ e τ τv} v :
  is_pure v ->
  (TC Γ ⊢ (λ τv, e) @ v : τ) ->
  (EXP Γ ⊢ (λ τv, e) @ v ≈ e.[v/] : τ).
Proof.
  intros v_val Happ.

  inversion Happ; subst.
  inversion X; subst.
  rename X into Hlam, X0 into Hv, X1 into He, τa into τv.

  assert (Hsubst : TC Γ ⊢ e.[v/] : τ). {
    apply (ty_subst He).
    intros.
    destruct x; simpl in *. {
      inversion H; subst.
      auto.
    } {
      constructor; auto.
    }
  }

  simple refine (relate_exprs _ _ _); auto.
  intros.

  replace (close ρ Happ) with (TCApp (close ρ Hlam) (close ρ Hv))
    by apply tc_unique.

  unfold μ.

  pose proof (by_μe_eq_μEntropy_app (close ρ Hlam) (close ρ Hv)).
  (* this simpl rewrites some implicits! remove with caution *)
  simpl in *.
  rewrite H.
  clear H.

  setoid_rewrite (pure_is_dirac (close ρ Hlam) I).
  rewrite meas_id_left.

  assert (is_pure v.[subst_of_WT_Env ρ]). {
    destruct v; try contradiction v_val; auto.
    apply pure_subst.
  }
  setoid_rewrite (pure_is_dirac (close ρ Hv) H).
  rewrite meas_id_left.

  do_elim_apply_in; subst.

  set (ty_subst1 _ _).
  set (close ρ Hsubst).
  clearbody t t0.
  fold (μ t) (μ t0).

  assert (e.[v/].[subst_of_WT_Env ρ] =
          e.[up (subst_of_WT_Env ρ)].[WT_Val_of_pure (close ρ Hv) H : Expr/])
    by autosubst.

  erewrite (μ_rewrite H0).
  auto.
Qed.

Print Assumptions beta_value.

Lemma apply_id_equiv {Γ τ e} :
  (TC Γ ⊢ e : τ) ->
  (EXP Γ ⊢ (λ τ, `O) @ e ≈ e : τ).
Proof.
  intro He.

  simple refine (relate_exprs _ _ _)
  ; try solve [repeat econstructor; eauto].

  intros.

  unfold μ.
  setoid_rewrite <- (project_same_integral _ 1) at 2.
  integrand_extensionality σ.
  unfold compose, eval_in.

  decide_eval as [v0 w0 ex0 u0]. {
    inversion ex0; subst; try absurd_Val.
    inversion X; subst.
    inversion H0; subst.
    simpl in *.
    inversion X1; subst; try absurd_Val.
    clear ex0 X H0 X1.

    decide_eval as [v4 w4 ex4 u4]; simpl.
    specialize (u4 (_, _) X0).
    inversion u4.
    subst.

    enough (v0 = v4) by (subst; nnr).
    exact (WT_Val_eq H1).
  } {
    decide_eval as [v1 w1 ex1 u1]; simpl.
    contradict not_ex. {
      eexists (_, _).
      repeat econstructor; eauto. {
        apply EPure'; simpl; auto.
      } {
        apply EPure'; simpl; auto.
      }
    }
  }
Qed.

Fixpoint is_simple (c : Ctx) : Prop :=
  match c with
  | c_hole => True
  | c_app_l c' _ | c_app_r _ c' | c_factor c' | c_plus_l c' _ | c_plus_r _ c' => is_simple c'
  | c_lam _ _ => False
  end.

Notation "e ^ n" := (rename (lift n) e).
Notation "e ↑" := (e ^ 1) (at level 3).

Lemma raise_O e : e ^ O = e.
Proof.
  unfold lift, rename.
  simpl.
  induction e; simpl; rewrite ?IHe; auto; f_equal; autosubst.
Qed.

Lemma ctx_rename_compose (S : Ctx) (f g : nat -> nat) :
  rename f (rename g S) = rename (f ∘ g) S.
Proof.
  unfold rename.
  revert f g.
  induction S; intros; simpl; rewrite ?IHS, ?H; auto; try autosubst.
  f_equal.
  assert (upren f ∘ upren g = upren (f ∘ g)). {
    compute.
    extensionality x.
    destruct x; auto.
  }
  rewrite <- H.
  auto.
Qed.

Lemma raise_S_i n e :
  e ^ (S n) = (e↑) ^ n.
Proof.
  rewrite ctx_rename_compose.
  f_equal.
  extensionality z.
  unfold compose, lift.
  rewrite plus_assoc.
  f_equal.
  rewrite plus_comm.
  auto.
Qed.

Lemma raise_S_o n e :
  e ^ (S n) = (e ^ n)↑.
Proof.
  rewrite ctx_rename_compose.
  auto.
Qed.

Lemma up_tc {Γ τ e} τ0 :
  (TC Γ ⊢ e : τ) ->
  (TC (extend Γ τ0) ⊢ e↑ : τ).
Proof.
  intros.
  rewrite rename_subst.
  eapply ty_ren; eauto.
Qed.

Definition subst_into_simple_defn Γ τe τo S :=
  forall e,
    (TC Γ ⊢ e : τe) ->
    (EXP Γ ⊢ (λ τe, S↑⟨`O⟩) @ e ≈ S⟨e⟩ : τo).

Lemma up_tcx {Γ τh τo τe C} :
  is_simple C ->
  (TCX Γ ⊢ C [Γ => τh] : τo) ->
  (TCX extend Γ τe ⊢ C↑ [τe :: Γ => τh] : τo).
Proof.
  intros simp HC.
  dependent induction HC
  ; try solve [econstructor
               ; eauto
               ; rewrite rename_subst
               ; eapply ty_ren
               ; eauto].
  contradiction simp.
Qed.

Lemma rename_simple (S : Ctx) (f : nat -> nat) :
  is_simple S -> is_simple (rename f S).
Proof.
  intros.
  induction S; try contradiction H; auto.
Qed.


Lemma pure_of_val {τ} (v : WT_Val τ) : is_pure v.
Proof.
  destruct v using WT_Val_rect; simpl; trivial.
Qed.

Lemma single_frame_case_app_l {Γ τe τa τo f e ea}:
  (TC Γ ⊢ ea : τa) ->
  (TC Γ ⊢ f : τe ~> τa ~> τo) ->
  (TC Γ ⊢ e : τe) ->
  is_val f ->
  let S1 := (c_app_l c_hole ea) in
  (EXP Γ ⊢ (λ τe, S1↑⟨f↑ @ `O⟩) @ e ≈ S1⟨f @ e⟩ : τo).
Proof.
  intros Hea Hf He f_val ?.
  subst S1.
  simpl.

  simple refine (relate_exprs _ _ _). {
    repeat econstructor; eauto. {
      rewrite rename_subst.
      eapply ty_ren; eauto.
    } {
      rewrite rename_subst.
      eapply ty_ren; eauto.
    }
  } {
    repeat econstructor; eauto.
  }

  intros.
  set (Hf' := rew <- _ in _).
  set (Hea' := rew <- _ in _).
  clearbody Hf' Hea'.
  simpl in *.

  unfold μ.
  rewrite !by_μe_eq_μEntropy_app.

  rewrite (pure_is_dirac (TCLam _) I).
  rewrite meas_id_left.

  inversion Hf; subst; try contradiction f_val.
  rename body into f_body, X into Hf_body.
  clear f_val.

  transitivity
    ((μ (close ρ He) >>=
        (fun ve =>
           μ (close ρ Hea) >>=
             (fun vea =>
                μ (ty_subst1 ve (body_subst ρ Hf_body)) >>=
                  (fun vfe =>
                     μEntropy >>= apply_in vfe vea
     )))) A).
  {
    integrand_extensionality ve.
    set (vlam := WT_Val_of_pure _ _).
    do_elim_apply_in.
    subst.
    clear vlam.

    set (ty_subst1 _ _).
    clearbody t.
    inversion t; subst.
    replace t with (TCApp X X0) by apply tc_unique.
    clear t.

    pose proof (by_μe_eq_μEntropy_app X X0).
    simpl in *. (* messes with implicits *)
    rewrite H.
    clear H.

    rewrite tonelli; auto.

    assert (τa0 = τa). {
      revert X0 Hea; clear; intros.
      eapply expr_type_unique; eauto.
      apply ty_subst1.
      apply body_subst.
      rewrite rename_subst.
      eapply ty_ren; eauto.
    }
    subst.

    replace (μ X0) with (μ (close ρ Hea)); swap 1 2. {
      unfold μ.
      extensionality A'.
      integrand_extensionality σ.
      set (ea↑.[up (subst_of_WT_Env ρ)].[ve : Expr/]) in *.
      assert (y = ea.[subst_of_WT_Env ρ]) by (subst y; autosubst).
      clearbody y.
      subst.
      replace (close ρ Hea) with X0 by apply tc_unique.
      reflexivity.
    }

    integrand_extensionality vea.

    replace (μ (ty_subst1 _ _)) with (μ X); auto.

    unfold μ.
    extensionality A'.
    dependent destruction X.

    rewrite by_μe_eq_μEntropy_app.
    rewrite (pure_is_dirac X1 I).
    rewrite (pure_is_dirac X2 (pure_of_val _)).
    rewrite 2 meas_id_left.

    integrand_extensionality σ.

    do_elim_apply_in; subst.
    replace (WT_Val_of_pure _ _) with ve by (apply WT_Val_eq; auto).

    set (body_subst _ _).
    clearbody t.

    generalize (ty_subst1 ve Hbody0).
    generalize (ty_subst1 ve t).
    clear.
    intros.

    match goal with
    | [ |- @eval_in ?e0' _ _ _ _ = @eval_in ?e1' _ _ _ _ ] =>
      set (e0 := e0') in *;
        set (e1 := e1') in *
    end.

    assert (e0 = e1) by (subst e0 e1; autosubst).
    clearbody e0 e1.
    subst.
    replace t with t0 by apply tc_unique.
    auto.
  } {
    setoid_rewrite by_μe_eq_μEntropy_app.

    rewrite meas_bind_assoc.
    setoid_rewrite (meas_bind_assoc (μ (close ρ He))).
    rewrite (tonelli (μ (close ρ Hf))); auto.
    integrand_extensionality ve.

    rewrite (pure_is_dirac (close ρ Hf) I).
    rewrite meas_id_left.

    do_elim_apply_in; subst.

    replace (μEntropy >>= _) with (μ (ty_subst1 ve Hbody)) by auto.
    rewrite tonelli; auto.

    replace (body_subst ρ Hf_body) with Hbody by apply tc_unique.
    auto.
  }
Qed.

Lemma single_frame_case_app_r {Γ τe τa τo f e ef}:
  (TC Γ ⊢ ef : τa ~> τo) ->
  (TC Γ ⊢ f : τe ~> τa) ->
  (TC Γ ⊢ e : τe) ->
  is_val f ->
  let S1 := (c_app_r ef c_hole) in
  (EXP Γ ⊢ (λ τe, S1↑⟨f↑ @ `O⟩) @ e ≈ S1⟨f @ e⟩ : τo).
Proof.
  intros Hef Hf He f_val.
  simpl.

  simple refine (relate_exprs _ _ _). {
    repeat econstructor; eauto. {
      rewrite rename_subst.
      eapply ty_ren; eauto.
    } {
      rewrite rename_subst.
      eapply ty_ren; eauto.
    }
  } {
    repeat econstructor; eauto.
  }

  intros.
  set (Hef' := rew <- _ in _).
  set (Hf' := rew <- _ in _).
  clearbody Hf' Hef'.
  simpl in *.

  unfold μ.
  rewrite !by_μe_eq_μEntropy_app.

  rewrite (pure_is_dirac (TCLam _) I).
  rewrite meas_id_left.

  set (WT_Val_of_pure _ _).
  destruct (elim_apply_in w) as [body' [Hbody' [Hvf_body H]]].
  setoid_rewrite H.
  subst w.
  inversion Hvf_body.
  subst body'.
  clear H Hvf_body.

  dependent destruction Hf; try contradiction f_val.
  rename body into f_body, Hf into Hf_body.
  clear f_val.
  simpl.

  transitivity
    ((μ (close ρ He) >>=
        (fun ve =>
           μ (close ρ Hef) >>=
             (fun vef =>
                μ (ty_subst1 ve (body_subst ρ Hf_body)) >>=
                  (fun vfe =>
                     μEntropy
                       >>= apply_in vef vfe)))) A).
  {
    integrand_extensionality ve.

    set (ty_subst1 _ _).
    clearbody t.
    dependent destruction t.

    rewrite by_μe_eq_μEntropy_app.

    rewrite tonelli; auto.

    assert (τa0 = τa). {
      enough ((τa0 ~> τr) = (τa ~> τr)). {
        inversion H; auto.
      }
      eapply expr_type_unique; eauto.
      apply ty_subst1.
      apply body_subst.
      auto.
    }
    subst.
    dependent destruction t2.
    dependent destruction t2_1.

    unfold μ at 1.
    rewrite by_μe_eq_μEntropy_app.
    rewrite meas_bind_assoc.

    rewrite (pure_is_dirac (TCLam _) I).
    rewrite (pure_is_dirac t2_2 (pure_of_val _)).
    rewrite 2 meas_id_left.

    do_elim_apply_in; subst.
    set (ty_subst1 _ _).
    clearbody t.
    fold (μ t).

    rewrite tonelli; auto.
    replace (μ t1) with (μ (close ρ Hef)) by (apply μ_rewrite; autosubst).
    integrand_extensionality vef.
    replace (μ (ty_subst1 _ _)) with (μ t) by (apply μ_rewrite; autosubst).
    auto.
  } {
    rewrite tonelli; auto.
    integrand_extensionality vef.

    unfold μ at 3.
    rewrite by_μe_eq_μEntropy_app.

    rewrite (pure_is_dirac (TCLam _) I).
    rewrite meas_id_left.
    rewrite meas_bind_assoc.
    integrand_extensionality ve.

    do_elim_apply_in; subst.
    do 2 set (ty_subst1 _ _).
    fold (μ t) (μ t0).
    f_equal.

    apply μ_rewrite.
    autosubst.
  }
Qed.

Lemma single_frame_case_factor {Γ τe f e}:
  (TC Γ ⊢ f : τe ~> ℝ) ->
  (TC Γ ⊢ e : τe) ->
  is_val f ->
  let S1 := c_factor c_hole in
  (EXP Γ ⊢ (λ τe, S1↑⟨f↑ @ `O⟩) @ e ≈ S1⟨f @ e⟩ : ℝ).
Proof.
  intros Hf He f_val.
  simpl.

  simple refine (relate_exprs _ _ _). {
    repeat econstructor; eauto.
    rewrite rename_subst.
    eapply ty_ren; eauto.
  } {
    repeat econstructor; eauto.
  }

  intros.

  set (Hf' := rew <- _ in _).
  clearbody Hf'.
  simpl in *.

  unfold μ.
  rewrite by_μe_eq_μEntropy_factor.
  setoid_rewrite by_μe_eq_μEntropy_app.
  rewrite by_μe_eq_μEntropy_app.

  dependent destruction Hf; try contradiction f_val.
  rename body into f_body, Hf into Hf_body.
  clear f_val.
  simpl.

  rewrite !(pure_is_dirac (TCLam _) I).
  rewrite !meas_id_left.
  rewrite meas_bind_assoc.

  integrand_extensionality ve.
  rewrite meas_bind_assoc.

  do 2 do_elim_apply_in; subst.

  do 2 set (ty_subst1 _ _).
  clearbody t t0.
  dependent destruction t.
  dependent destruction t.

  pose proof (by_μe_eq_μEntropy_factor (TCApp t1 t2)).
  simpl in *. (* implicit rewriting *)
  rewrite H.

  rewrite <- meas_bind_assoc.
  fold (μ t0).

  repeat f_equal.

  setoid_rewrite by_μe_eq_μEntropy_app.
  rewrite (pure_is_dirac t1 I).
  rewrite (pure_is_dirac t2 (pure_of_val _)).
  rewrite !meas_id_left.

  do_elim_apply_in; subst.
  set (ty_subst1 _ _).
  clearbody t.
  fold (μ t).

  apply μ_rewrite.
  autosubst.
Qed.

Lemma single_frame_case_plus_l {Γ τe f e er}:
  (TC Γ ⊢ er : ℝ) ->
  (TC Γ ⊢ f : τe ~> ℝ) ->
  (TC Γ ⊢ e : τe) ->
  is_val f ->
  let S1 := (c_plus_l c_hole er) in
  (EXP Γ ⊢ (λ τe, S1↑⟨f↑ @ `O⟩) @ e ≈ S1⟨f @ e⟩ : ℝ).
Proof.
  intros Her Hf He f_val.

  simple refine (relate_exprs _ _ _). {
    repeat econstructor; auto;
      rewrite rename_subst;
      eapply ty_ren; eauto.
  } {
    repeat econstructor; eauto.
  }

  intros.
  set (Hf' := rew <- _ in _).
  set (Her' := rew <- _ in _).
  clearbody Hf' Her'.
  simpl in *.

  unfold μ.
  rewrite by_μe_eq_μEntropy_plus.
  rewrite !by_μe_eq_μEntropy_app.
  setoid_rewrite by_μe_eq_μEntropy_app.

  rewrite (pure_is_dirac (TCLam _) I).
  rewrite meas_id_left.

  rewrite meas_bind_assoc.
  setoid_rewrite meas_bind_assoc.
  rewrite (tonelli (μ (close ρ Hf))); auto.

  integrand_extensionality ve.

  do_elim_apply_in; subst.
  set (ty_subst1 _ _).
  clearbody t.
  dependent destruction t.
  dependent destruction t1.

  pose proof (by_μe_eq_μEntropy_plus (TCApp t1_1 t1_2) t2).
  simpl in *. (* implicits *)
  rewrite H; clear H.

  unfold μ at 1.
  rewrite by_μe_eq_μEntropy_app.

  assert (τa = τe). {
    enough ((τa ~> ℝ) = (τe ~> ℝ)). {
      inversion H; auto.
    }
    eapply expr_type_unique; eauto.
    apply ty_subst1.
    apply body_subst.
    auto.
  }
  subst.

  replace (μ (close ρ Hf)) with (μ t1_1)
    by (apply μ_rewrite; autosubst).
  rewrite meas_bind_assoc.
  integrand_extensionality vf.

  rewrite (pure_is_dirac t1_2 (pure_of_val _)).
  rewrite meas_id_left.
  replace (WT_Val_of_pure _ _) with ve by (apply WT_Val_eq; auto).
  integrand_extensionality vl.
  f_equal.

  apply μ_rewrite; autosubst.
Qed.

Lemma single_frame_case_plus_r {Γ τe f e el}:
  (TC Γ ⊢ el : ℝ) ->
  (TC Γ ⊢ f : τe ~> ℝ) ->
  (TC Γ ⊢ e : τe) ->
  is_val f ->
  let S1 := (c_plus_r el c_hole) in
  (EXP Γ ⊢ (λ τe, S1↑⟨f↑ @ `O⟩) @ e ≈ S1⟨f @ e⟩ : ℝ).
Proof.
  intros Hel Hf He f_val.
  simpl.

  (* does this depend on commutativity of addition? no! I'm just lazy *)
  transitivity ((λ τe, (f↑ @ `O) +! el↑) @ e). {
    eapply compat_app; [| eapply fundamental_property]; eauto.
    apply compat_lam.
    apply add_comm_related. {
      apply up_tc.
      auto.
    } {
      repeat econstructor; eauto.
      apply up_tc.
      auto.
    }
  }

  transitivity ((f @ e) +! el). {
    apply single_frame_case_plus_l; auto.
  }

  apply add_comm_related; auto.
  repeat econstructor; eauto.
Qed.

Lemma rename_plugged_simple S σ e :
  is_simple S ->
  rename σ (S⟨e⟩) = (rename σ S)⟨rename σ e⟩.
Proof.
  intros.
  induction S; simpl; auto; fold rename; rewrite ?IHS; auto.
  contradiction H.
Qed.

Definition is_simple_single (c : Ctx) : Prop :=
  match c with
  | c_app_l c_hole _
  | c_app_r _ c_hole
  | c_factor c_hole
  | c_plus_l c_hole _
  | c_plus_r _ c_hole
    => True
  | _ => False
  end.

Lemma single_is_simple {C} :
  is_simple_single C -> is_simple C.
Proof.
  intros.
  destruct C; try destruct C; tauto.
Qed.

Lemma simple_plug_simple {S S' : Ctx} :
  is_simple S ->
  is_simple S' ->
  is_simple (plug_ctx S S').
Proof.
  intros.
  induction S; try contradiction H; auto.
Defined.

Lemma tc_ctx_single_rect {Γ}
      (P : forall S τh τ,
          is_simple S ->
          (TCX Γ ⊢ S[Γ => τh] : τ) ->
          Type) :
  (forall τh, P c_hole τh τh I (TCXHole Γ τh)) ->
  (forall (τh τm τ : Ty) (S1 S : Ctx)
          (HS1 : TCX Γ ⊢ S1[Γ => τm] : τ)
          (HS : TCX Γ ⊢ S[Γ => τh] : τm)
          (S_simple : is_simple S)
          (S1_single : is_simple_single S1),
      P S τh τm S_simple HS ->
      P (plug_ctx S1 S) τh τ
        (simple_plug_simple (single_is_simple S1_single) S_simple)
        (tc_plug_ctx HS1 HS)) ->
  forall τh τ S S_simple HS,
    P S τh τ S_simple HS.
Proof.
  intros case_hole case_composition.
  intros.
  revert τ τh HS.
  induction S;
    intros;
    try contradiction S_simple;
    dependent destruction HS.
  {
    destruct S_simple.
    apply case_hole.
  } {
    specialize (case_composition _ _ _ _ _ (TCXApp_l _ _ (TCXHole _ _) t) HS).
    specialize (case_composition S_simple I).
    apply case_composition.
    apply IHS.
  } {
    specialize (case_composition _ _ _ _ _ (TCXApp_r _ _ t (TCXHole _ _)) HS).
    specialize (case_composition S_simple I).
    apply case_composition.
    apply IHS.
  } {
    specialize (case_composition _ _ _ _ _ (TCXFactor _ _ (TCXHole _ _)) HS).
    specialize (case_composition S_simple I).
    apply case_composition.
    apply IHS.
  } {
    specialize (case_composition _ _ _ _ _ (TCXPlus_l _ _ (TCXHole _ _) t) HS).
    specialize (case_composition S_simple I).
    apply case_composition.
    apply IHS.
  } {
    specialize (case_composition _ _ _ _ _ (TCXPlus_r _ _ t (TCXHole _ _)) HS).
    specialize (case_composition S_simple I).
    apply case_composition.
    apply IHS.
  }
Qed.

Lemma rename_plug_ctx C C' σ :
  is_simple C ->
  rename σ (plug_ctx C C') = plug_ctx (rename σ C) (rename σ C').
Proof.
  intros.
  induction C; intros; simpl; try setoid_rewrite IHC; auto.
  contradiction H.
Qed.

Lemma compat_plug {Γo τo Γh τh C e0 e1} :
  (TCX Γo ⊢ C[Γh => τh] : τo) ->
  (EXP Γh ⊢ e0 ≈ e1 : τh) ->
  (EXP Γo ⊢ C⟨e0⟩ ≈ C⟨e1⟩ : τo).
Proof.
  intros HC Hes.
  dependent induction HC. {
    auto.
  } {
    eapply compat_app; auto.
    apply fundamental_property; auto.
  } {
    eapply compat_app; auto.
    apply fundamental_property; auto.
  } {
    apply compat_factor; auto.
  } {
    apply compat_plus; auto.
    apply fundamental_property; auto.
  } {
    apply compat_plus; auto.
    apply fundamental_property; auto.
  } {
    apply compat_lam; auto.
  }
Qed.

(* theorem 24 *)
Theorem subst_into_simple {Γo Γi τe τo S} :
  is_simple S ->
  (TCX Γo ⊢ S[Γi => τe] : τo) ->
  subst_into_simple_defn Γo τe τo S.
Proof.
  intros S_simple HSC e He.

  assert (Γi = Γo). {
    clear He.
    revert τo HSC.
    induction S
    ; intros
    ; inversion HSC
    ; subst
    ; try contradiction S_simple
    ; try eapply IHSC
    ; eauto.
  }
  subst.
  rename Γo into Γ.

  pose proof (tc_plug He HSC).
  revert X.

  (* revert e He. *)

  generalize (@eq_refl _ τe).
  revert τo S S_simple HSC.

  refine (tc_ctx_single_rect
            (fun S' τh τ S_simple HSC' =>
               τh = τe ->
               (* forall e, *)
               (*   (TC Γ ⊢ e : τe) -> *)
                 (TC Γ ⊢ S'⟨e⟩ : τ) ->
                 (EXP Γ ⊢ (λ τe, S'↑⟨`O⟩) @ e ≈ S'⟨e⟩ : τ)
            )
            _ _ _). {
    intros.
    simpl in *.
    subst.
    exact (apply_id_equiv X).
  } {
    intros.
    subst.
    specialize (H eq_refl (tc_plug He HS)).

    transitivity ((λ τe, S1↑⟨(λ τe, S↑↑⟨`O⟩) @ `O⟩) @ e). {
      (* "by theorem 22" *)
      eapply compat_app; [| solve [eapply fundamental_property; eauto]].
      apply compat_lam.

      pose proof @beta_value (extend Γ τe) (S↑↑⟨`O⟩).
      specialize (H0 τm τe `O I).
      assert (TC extend Γ τe ⊢ (λ τe, ((S ↑) ↑)⟨` 0⟩) @ ` 0 : τm). {
        repeat econstructor.
        eapply up_tcx in HS; auto.
        eapply rename_simple in S_simple.
        eapply up_tcx in HS; eauto.
        refine (tc_plug (TCVar _) HS).
        auto.
      }
      specialize (H0 X0).
      clear X0.

      pose proof single_is_simple S1_single as S1_simple.

      rewrite rename_plug_ctx; auto.
      rewrite plug_plug_ctx.

      symmetry.
      eapply up_tcx in HS1; auto.
      eapply compat_plug; eauto.
      assert (S↑⟨`O⟩ = S↑↑⟨`O⟩.[`O/]). {
        revert S_simple; clear; intros.
        induction S; simpl; auto;
          try solve [setoid_rewrite IHS; auto; f_equal; autosubst].
        contradiction S_simple.
      }

      rewrite H1.
      exact H0.
    }

    transitivity (S1⟨(λ τe, S↑⟨`O⟩) @ e⟩). {
      set (f := λ τe, S↑⟨`O⟩).
      replace (λ τe, S↑↑⟨`O⟩) with (f↑); swap 1 2. {
        revert S_simple; clear; intros.
        subst f.
        simpl.
        f_equal.

        rewrite rename_plugged_simple; swap 1 2. {
          apply rename_simple.
          auto.
        } {
          f_equal.
          rewrite 2 ctx_rename_compose.
          auto.
        }
      }

      assert (Hf : TC Γ ⊢ f : τe ~> τm). {
        constructor.
        refine (tc_plug (TCVar _) (up_tcx _ HS)); auto.
      }

      destruct S1; try destruct S1; try contradiction S1_single. {
        inversion HS1; subst.
        inversion X0; subst.
        eapply single_frame_case_app_l; eauto.
      } {
        inversion HS1; subst.
        inversion X1; subst.
        eapply single_frame_case_app_r; eauto.
      } {
        inversion HS1; subst.
        inversion X0; subst.
        apply single_frame_case_factor; auto.
      } {
        inversion HS1; subst.
        inversion X0; subst.
        apply single_frame_case_plus_l; auto.
      } {
        inversion HS1; subst.
        inversion X1; subst.
        apply single_frame_case_plus_r; auto.
      }
    }

    rewrite plug_plug_ctx.
    erewrite compat_plug; eauto.
    apply fundamental_property.
    eapply tc_plug; eauto.
    eapply tc_plug; eauto.
  }
Qed.

Print Assumptions subst_into_simple.
