Require Import Reals.
Require Import List.
Require Import Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import nnr.
Require Import cube.
Require Export entropy.
Require Import utils.
Require Import List.
Require Import FinFun.
Require Import RelationClasses.

Require Export Autosubst.Autosubst.

Local Open Scope ennr.

Inductive Effect :=
| ObsR
| ObsNone
.

Reserved Infix "≼" (at level 70, no associativity).

Definition subeffect (ϕ0 ϕ1 : Effect) : Prop :=
  match ϕ0, ϕ1 with
  | ObsNone, ObsR => False
  | _, _ => True
  end.
Infix "≼" := subeffect.

Inductive Ty :=
| ℝ : Ty
| Arrow : Effect -> Ty -> Ty -> Ty
.
Notation "x ~~ ϕ ~> y" := (Arrow ϕ x y) (at level 69, right associativity, y at level 70).

Instance subeffect_refl : Reflexive subeffect.
Proof.
  intro ϕ.
  destruct ϕ; cbn; auto.
Qed.

Lemma effect_eq_dec : forall (ϕ ϕ' : Effect), {ϕ = ϕ'} + {ϕ <> ϕ'}.
Proof.
  decide equality.
Qed.

Lemma ty_eq_dec : forall (τ τ' : Ty), {τ = τ'} + {τ <> τ'}.
Proof.
  decide equality.
  apply effect_eq_dec.
Defined.

Inductive unop :=
| Log
| Exp
.

Inductive binop :=
| Add
| Mult
| CheckedNonZeroMult
.

Definition unop_effect (op : unop) : Effect := ObsR.

Definition binop_effect (op : binop) : Effect :=
  match op with
  | Mult => ObsNone
  | _ => ObsR
  end.

Definition effect_compose (ϕ0 ϕ1 : Effect) : Effect :=
  match ϕ0, ϕ1 with
  | ObsR, ObsR => ObsR
  | _, _ => ObsNone
  end.

Lemma effect_compose_id_r ϕ : effect_compose ϕ ObsR = ϕ.
Proof.
  destruct ϕ; reflexivity.
Qed.

Definition δϕ1 (op : unop) : Effect -> Effect := effect_compose (unop_effect op).
Definition δϕ2 (op : binop) : Effect -> Effect := effect_compose (binop_effect op).

Definition δ1 (op : unop) : R -> option R :=
  match op with
  | Log =>
    fun x =>
      match Rlt_dec 0 x with
      | left H => Some (ln x)
      | right _ => None
      end
  | Exp => fun x => Some (exp x)
  end.

Definition δ2 (op : binop) : R -> R -> option R :=
  match op with
  | Add => fun x y => Some (x + y)%R
  | Mult => fun x y => Some (x * y)%R
  | CheckedNonZeroMult =>
    fun x y =>
      if Req_EM_T x 0
      then None
      else Some (x * y)%R
  (* | Mult => Rmult *)
  end.

(** It becomes useful for dealing with the standard library derivatives to know
    partiality before applying the last argument. Kinda a hack, but oh well. *)

Definition weird_δ2 (op : binop) : R -> option (R -> R) :=
  match op with
  | Add => fun x => Some (fun y => x + y)%R
  | Mult => fun x => Some (fun y => x * y)%R
  | CheckedNonZeroMult =>
    fun x =>
      if Req_EM_T x 0
      then None
      else Some (fun y => x * y)%R
  end.

Lemma weird_δ2_correct op x y :
  δ2 op x y = weird_δ2 op x <*> Some y.
Proof.
  destruct op; cbn; auto.
  destruct Req_EM_T; auto.
Qed.

(* if {v0} = op^-1(·)({v})
   then return v0 *)
Definition δ1_inv (op : unop) : R -> option R :=
  (match op with
   | Log => δ1 Exp
   | Exp => δ1 Log
   end)%R.

(* if {v1} = op^-1(v0, ·)({v})
   then return v1 *)
Definition δ2_inv (op : binop) (v0 : R) (v : R) : option R :=
  (match op with
   | Add => Some (v - v0)
   | Mult => None
   | CheckedNonZeroMult =>
     if Req_EM_T v0 0
     then None
     else Some (v / v0)
   end)%R.

Lemma δ1_inv_sound {op v0 v} :
  δ1_inv op v = Some v0 ->
  δ1 op v0 = Some v.
Proof.
  destruct op; cbn; intros; try inject H. {
    destruct Rlt_dec. {
      f_equal.
      apply ln_exp.
    } {
      contradict n.
      apply exp_pos.
    }
  } {
    destruct Rlt_dec; inject H.
    rewrite exp_ln; auto.
  }
Qed.

Lemma δ1_inv_complete {op v0 v} :
  (* unop_effect op = ObsR -> (* This is always true for now *) *)
  δ1 op v0 = Some v ->
  δ1_inv op v = Some v0.
Proof.
  destruct op; cbn; intros. {
    destruct Rlt_dec; inject H.
    rewrite exp_ln; auto.
  } {
    inject H.
    destruct Rlt_dec. {
      rewrite ln_exp.
      auto.
    } {
      contradict n.
      apply exp_pos.
    }
  }
Qed.

Lemma δ2_inv_sound {op v0 v1 v} :
  δ2_inv op v0 v = Some v1 ->
  δ2 op v0 v1 = Some v.
Proof.
  destruct op; cbn; intros;
    try destruct Req_EM_T;
    inject H;
    f_equal;
    field;
    assumption.
Qed.

Lemma δ2_inv_complete {op v0 v1 v} :
  binop_effect op = ObsR ->
  δ2 op v0 v1 = Some v ->
  δ2_inv op v0 v = Some v1.
Proof.
  destruct op; try discriminate; cbn; intros. {
    inject H0.
    f_equal.
    ring.
  } {
    destruct Req_EM_T; try discriminate.
    inject H0.
    f_equal.
    field.
    auto.
  }
Qed.

(* Need this for opacity without having to deal with classical axioms, maybe
   there's a nicer way to package it? *)
Lemma δ2_inv_checked_fail r :
      δ2_inv CheckedNonZeroMult 0 r = None.
Proof.
  cbn.
  destruct Req_EM_T; auto; contradiction.
Qed.
Global Opaque δ1_inv δ2_inv.

(* Lemma δ1_unique_inv_uniqueness op v v0 v0' : *)
(*   δ1 op v0 = Some v -> *)
(*   δ1_unique_inv op v = Some v0' -> *)
(*   v0 = v0'. *)
(* Proof. *)
(*   intros. *)
(*   apply δ1_unique_inv_is_complete in H. *)
(*   rewrite H in H0. *)
(*   inject H0. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma δ2_unique_inv_uniqueness op v v0 v1 v1' : *)
(*   δ2 op v0 v1 = Some v -> *)
(*   δ2_unique_inv op v0 v = Some v1' -> *)
(*   v1 = v1'. *)
(* Proof. *)
(*   intros. *)
(*   destruct op; cbn in *; try destruct Req_EM_T; try inject H0; try inject H; field; auto. *)
(* Qed. *)

(* Lemma δ2_unique_inv_minimal op v v0 v1 : *)
(*   δ2 op v0 v1 = None -> *)
(*   δ2_inv op v0 v <> Some v1. *)
(* Proof. *)
(*   repeat intro. *)
(*   apply δ2_inv_sound in H0. *)
(*   rewrite H in H0. *)
(*   discriminate. *)
(* Qed. *)

Definition δ1_partial_deriv (op : unop) (v0 : R) : R :=
  match op with
  | Log => / v0
  | Exp => exp v0
  end.

Definition δ2_partial_deriv (op : binop) (v0 v1 : R) : R :=
  match op with
  | Add => 1
  | Mult | CheckedNonZeroMult => v0
  end.

Lemma δ1_partial_deriv_correct op v0 :
  forall junk,
    δ1 op v0 <> None ->
    derivable_pt_lim (fun v0' : R => fromOption junk (δ1 op v0')) v0 (δ1_partial_deriv op v0).
Proof.
  intros.
  destruct op. {
    cbn in H.
    destruct Rlt_dec; try contradiction.
    hnf; intros.
    destruct (derivable_pt_lim_ln _ r eps H0) as [δ Hδ].
    assert (0 < Rmin δ v0)%R. {
      destruct δ; cbn in *.
      unfold Rmin.
      destruct Rle_dec; auto.
    }
    exists (mkposreal _ H1); cbn; clear H1.
    intros.
    assert (Rabs h < δ)%R. {
      clear_except H2.
      unfold Rmin in *.
      destruct Rle_dec;
        try apply Rnot_le_lt in n;
        try Fourier.fourier.
    }
    specialize (Hδ h H1 H3).
    unfold compose.
    destruct (Rlt_dec 0 v0); try contradiction.
    destruct Rlt_dec. {
      exact Hδ.
    }

    contradict n.
    unfold Rabs, Rmin in *.
    destruct Rle_dec, (Rcase_abs h); Fourier.fourier.
  } {
    apply derivable_pt_lim_exp.
  }
Qed.

Lemma δ2_partial_deriv_correct op v0 v1 :
  forall junk,
    δ2 op v0 v1 <> None ->
    derivable_pt_lim (fun v1' : R => fromOption junk (δ2 op v0 v1')) v1 (δ2_partial_deriv op v0 v1).
Proof.
  intros.
  destruct op; try discriminate H; unfold compose; cbn in *. {
    pose proof (derivable_pt_lim_plus (const v0) id v1 0 1).
    specialize (H0 (derivable_pt_lim_const _ _) (derivable_pt_lim_id _)).
    ring_simplify in H0.
    exact H0.
  } {
    pose proof (derivable_pt_lim_mult (const v0) id v1 0 1).
    specialize (H0 (derivable_pt_lim_const _ _) (derivable_pt_lim_id _)).
    ring_simplify in H0.
    exact H0.
  } {
    destruct Req_EM_T; try contradiction; cbn.
    pose proof (derivable_pt_lim_mult (const v0) id v1 0 1).
    specialize (H0 (derivable_pt_lim_const _ _) (derivable_pt_lim_id _)).
    ring_simplify in H0.
    exact H0.
  }
Qed.
Global Opaque δ1_partial_deriv δ2_partial_deriv.

Lemma δ1_partially_derivable op :
  partially_derivable (δ1 op).
Proof.
  intros v0 junk H.
  exists (δ1_partial_deriv op v0).
  apply δ1_partial_deriv_correct; auto.
Qed.

Lemma δ2_partially_derivable op v0 :
  partially_derivable (δ2 op v0).
Proof.
  intros v1 junk H.
  exists (δ2_partial_deriv op v0 v1).
  apply δ2_partial_deriv_correct; auto.
Qed.

(* u for untyped *)
Inductive u_expr :=
| u_app (uf ua : u_expr)
| u_factor (u : u_expr)
| u_sample
| u_observe (u0 u1 : u_expr)
| u_unop (op : unop) (u : u_expr)
| u_binop (op : binop) (ul ur : u_expr)
| u_real (r : R)
| u_lam (τ : Ty) (body : {bind u_expr})
| u_var (x : var)
| u_hide_observable (u : u_expr)
.

Definition is_pure (e : u_expr) : Prop :=
  match e with
  | u_real _ | u_lam _ _ | u_var _ => True
  | _ => False
  end.

Instance Ids_u_expr : Ids u_expr. derive. Defined.
Instance Rename_u_expr : Rename u_expr. derive. Defined.
Instance Subst_u_expr : Subst u_expr. derive. Defined.
Instance SubstLemmas_u_expr : SubstLemmas u_expr. derive. Defined.

Definition Env (T : Type) := list T.
Definition empty_env {T : Type} : Env T := nil.
Notation "·" := empty_env.

Fixpoint lookup {T} (ρ : Env T) x : option T :=
  match ρ with
  | nil => None
  | v :: ρ' =>
    match x with
    | O => Some v
    | S x' => lookup ρ' x'
    end
  end.

Inductive expr (Γ : Env Ty) : Ty -> Effect -> Type :=
| e_real (r : R) : expr Γ ℝ ObsNone
| e_var {τ} (x : var)
        (H : lookup Γ x = Some τ)
  : expr Γ τ ObsNone
| e_lam {τa τr ϕ}
        (body : expr (τa :: Γ) τr ϕ)
  : expr Γ (τa ~~ ϕ ~> τr) ObsNone
| e_app {τa τr ϕa ϕf ϕ}
        (ef : expr Γ (τa ~~ ϕ ~> τr) ϕf)
        (ea : expr Γ τa ϕa)
  : expr Γ τr ϕ
| e_factor {ϕ} (e : expr Γ ℝ ϕ)
  : expr Γ ℝ ObsNone
| e_sample
  : expr Γ ℝ ObsR
| e_observe {ϕ0}
            (e0 : expr Γ ℝ ϕ0)
            (e1 : expr Γ ℝ ObsR)
  : expr Γ ℝ ObsNone
| e_unop {ϕ}
         (op : unop)
         (e : expr Γ ℝ ϕ)
  : expr Γ ℝ ϕ
| e_binop {ϕl ϕr ϕ}
          (op : binop)
          (Hϕ : ϕ = δϕ2 op ϕr)
          (el : expr Γ ℝ ϕl)
          (er : expr Γ ℝ ϕr)
  : expr Γ ℝ ϕ
| e_hide_observable (e : expr Γ ℝ ObsR)
  : expr Γ ℝ ObsNone
.

Arguments e_real {Γ} r.
Arguments e_var {Γ τ} x H.
Arguments e_lam {Γ τa τr ϕ} body.
Arguments e_app {Γ τa τr ϕa ϕf ϕ} ef ea.
Arguments e_factor {Γ ϕ} e.
Arguments e_sample {Γ}.
Arguments e_observe {Γ ϕ0} e0 e1.
Arguments e_unop {Γ ϕ} op e.
Arguments e_binop {Γ ϕl ϕr ϕ} op Hϕ el er.
Arguments e_hide_observable {Γ} e.

Fixpoint erase {Γ τ ϕ} (e : expr Γ τ ϕ) : u_expr :=
  match e with
  | e_real r => u_real r
  | e_var x _ => u_var x
  | @e_lam _ τa τr _ body => u_lam τa (erase body)
  | e_app ef ea => u_app (erase ef) (erase ea)
  | e_factor e => u_factor (erase e)
  | e_sample => u_sample
  | e_observe el er => u_observe (erase el) (erase er)
  | e_unop op e => u_unop op (erase e)
  | e_binop op Hϕ el er => u_binop op (erase el) (erase er)
  | e_hide_observable e => u_hide_observable (erase e)
  end.
Coercion erase' {Γ τ ϕ} : expr Γ τ ϕ -> u_expr := erase.
Arguments erase' / {_ _ _} _.

Lemma expr_type_unique {Γ τ0 ϕ0 τ1 ϕ1} (e0 : expr Γ τ0 ϕ0) (e1 : expr Γ τ1 ϕ1) :
  erase e0 = erase e1 ->
  τ0 = τ1 /\ ϕ0 = ϕ1.
Proof.
  intros Heq.
  revert τ1 ϕ1 e1 Heq.
  dependent induction e0; intros;
    dependent destruction e1;
    inversion Heq; subst;
      try (split; auto; [idtac]);
    auto.
  {
    clear Heq.
    rewrite H0 in H.
    inversion H.
    auto.
  } {
    f_equal; eapply IHe0; eauto.
  } {
    specialize (IHe0_1 _ _ _ H0).
    inject IHe0_1.
    inject H.
    auto.
  } {
    eapply IHe0; eauto.
  } {
    edestruct IHe0_2; eauto; subst.
    auto.
  }
Qed.

Lemma erase_injective Γ τ ϕ : Injective (@erase Γ τ ϕ).
Proof.
  intro x.
  dependent induction x;
    intros y Hxy;
    dependent destruction y;
    inversion Hxy; subst; auto.
  {
    f_equal.
    apply proof_irrelevance.
  } {
    f_equal.
    apply IHx; auto.
  } {
    pose proof expr_type_unique x1 y1 H0.
    pose proof expr_type_unique x2 y2 H1.
    intuition idtac; subst.
    rewrite (IHx1 y1), (IHx2 y2); auto.
  } {
    pose proof expr_type_unique x y H0.
    inject H.
    rewrite (IHx y); auto.
  } {
    pose proof expr_type_unique x1 y1 H0.
    inject H.
    rewrite (IHx1 y1), (IHx2 y2); auto.
  } {
    rewrite (IHx y); auto.
  } {
    pose proof expr_type_unique x1 y1 H1.
    pose proof expr_type_unique x2 y2 H2.
    inject H.
    inject H0.
    d_destruct Hϕ0.
    rewrite (IHx1 y1), (IHx2 y2); auto.
  } {
    erewrite IHx; eauto.
  }
Qed.
Arguments erase_injective {_ _ _ _} _.

Ltac inject_erase_directly :=
  match goal with
  | [ H : erase ?x = erase ?y |- _ ] =>
    apply erase_injective in H;
    try subst x
  end.

Ltac match_erase_eqs :=
  let H := fresh "H" in
  let H' := fresh "H" in
  let H'' := fresh "H" in
  match goal with
  | [H0 : erase ?x = ?s, H1 : erase ?y = ?s |- _ ] =>
    pose proof (eq_trans H0 (eq_sym H1)) as H;
    let z := type of y in
    match type of x with
    | z => idtac
    | expr · ?τ ?ϕ =>
      pose proof (expr_type_unique _ _ H) as [H' H''];
      (subst τ || d_destruct H');
      (subst ϕ || d_destruct H'')
    end;
    apply erase_injective in H;
    subst x
  end;
  clear_dups.

Ltac subst_erase_eq :=
  match goal with
  | [ H : erase ?e = _, H' : context [ erase ?e ] |- _ ] =>
    rewrite H in H';
      try clear H e
  end.

(* d_destruct is often slow, do don't use unless we need *)
(* TODO: speed up even more for exprs *)
Ltac expr_destruct e :=
  match type of e with
  | expr _ (_ ~~ _ ~> _) _ => d_destruct e
  | expr _ ℝ _ => d_destruct e
  | expr _ _ _ => destruct e
  end.

Ltac inject_erased :=
  let go e H :=
      expr_destruct e; inject H
  in match goal with
     | [ H : erase ?e = u_app _ _ |- _ ] => go e H
     | [ H : erase ?e = u_factor _ |- _ ] => go e H
     | [ H : erase ?e = u_sample |- _ ] => expr_destruct e; try inject H
     | [ H : erase ?e = u_observe _ _ |- _ ] => go e H
     | [ H : erase ?e = u_unop _ _ |- _ ] => go e H
     | [ H : erase ?e = u_binop _ _ _ |- _ ] => go e H
     | [ H : erase ?e = u_real _ |- _ ] => go e H
     | [ H : erase ?e = u_lam _ _ |- _ ] => go e H
     | [ H : erase ?e = u_var _ |- _ ] => go e H
     | [ H : erase ?e = u_hide_observable _ |- _ ] => go e H
     end.

Ltac elim_erase_eqs :=
  progress repeat (subst_erase_eq
                   || inject_erase_directly
                   || match_erase_eqs
                   || inject_erased);
  clear_dups.

Ltac elim_sig_exprs :=
  let doit Γ τ pair stac :=
      (let e := fresh "e" in
       let He := fresh "H" e in
       destruct pair as [e He];
       stac;
       asimpl in He) in
  progress repeat
           match goal with
           | [ H : context [ @proj1_sig (expr ?Γ ?τ ?ϕ) _ ?pair ] |- _ ] =>
             doit Γ τ pair ltac:(cbn in H)
           | [ |- context [ @proj1_sig (expr ?Γ ?τ ?ϕ) _ ?pair ] ] =>
             doit Γ τ pair ltac:(cbn)
           end.

Ltac generalize_refl target :=
  let t := fresh "t" in
  let t' := fresh "t" in
  let Ht := fresh "Ht" in
  set (t' := target) in *;
  set (Ht := @eq_refl _ t') in *;
  clearbody Ht;
  set (t := t') in *;
  change (t = t') in Ht;
  clearbody t;
  subst t'.

Definition is_val (e : u_expr) : Prop :=
  match e with
  | u_real _ | u_lam _ _ => True
  | _ => False
  end.

Lemma is_val_unique {e : u_expr} (iv0 iv1 : is_val e) :
  iv0 = iv1.
Proof.
  destruct e; try contradiction; destruct iv0, iv1; auto.
Qed.

Inductive val τ :=
  mk_val (e : expr · τ ObsNone) (H : is_val e).
Arguments mk_val {τ} e H.
Coercion expr_of_val {τ} : val τ -> expr · τ ObsNone :=
  fun v => let (e, _) := v in e.

Lemma val_eq {τ} {v0 v1 : val τ} :
  v0 = v1 :> expr · τ ObsNone ->
  v0 = v1 :> val τ.
Proof.
  intros.
  destruct v0, v1.
  cbn in *.
  subst.
  rewrite (is_val_unique H0 H1).
  auto.
Qed.

Definition v_real r : val ℝ :=
  mk_val (e_real r) I.

Definition v_lam {τa τr ϕ} body : val (τa ~~ ϕ ~> τr) :=
  mk_val (e_lam body) I.

Definition rewrite_v_real r : e_real r = v_real r := eq_refl.
Definition rewrite_v_lam {τa τr ϕ} body :
  e_lam body = @v_lam τa τr ϕ body := eq_refl.

Lemma val_arrow_rect {τa τr ϕ}
      (P : val (τa ~~ ϕ ~> τr) -> Type)
      (case_lam : forall body, P (v_lam body)) :
  forall v, P v.
Proof.
  intros.
  destruct v as [v Hv].
  dependent destruction v; try contradiction Hv.
  destruct Hv.
  apply case_lam.
Defined.

Lemma val_real_rect
      (P : val ℝ -> Type)
      (case_real : forall r, P (v_real r)) :
  forall v, P v.
Proof.
  intros.
  destruct v as [v Hv].
  dependent destruction v; try contradiction Hv.
  destruct Hv.
  apply case_real.
Defined.

Lemma wt_val_rect {τ}
      (P : val τ -> Type)
      (case_real :
         forall r (τeq : ℝ = τ),
           P (rew τeq in v_real r))
      (case_lam :
         forall {τa τr ϕ}
                (τeq : (τa ~~ ϕ ~> τr) = τ)
                body,
           P (rew τeq in v_lam body)) :
  forall v, P v.
Proof.
  intros.
  destruct τ. {
    apply val_real_rect.
    intros.
    exact (case_real r eq_refl).
  } {
    apply val_arrow_rect.
    intros.
    exact (case_lam _ _ _ eq_refl body).
  }
Qed.

Ltac destruct_val wt_v :=
  match (type of wt_v) with
  | val ℝ =>
    destruct wt_v using val_real_rect
  | val (?τa ~~ ?ϕ ~> ?τr) =>
    destruct wt_v using val_arrow_rect
  | val ?τ =>
    destruct wt_v using wt_val_rect
  end.

Lemma for_absurd_val {τ} {v : val τ} {e : expr · τ ObsNone} :
  (expr_of_val v) = e ->
  is_val e.
Proof.
  intros.
  destruct v.
  subst.
  auto.
Qed.

Ltac absurd_val :=
  match goal with
  | [ H : (expr_of_val _) = _ |- _ ] =>
    contradiction (for_absurd_val H)
  | [ H : _ = (expr_of_val _) |- _ ] =>
    contradiction (for_absurd_val (eq_sym H))
  end.

Inductive dep_env {A} (v : A -> Type) : Env A -> Type :=
| dep_nil : dep_env v ·
| dep_cons {τ Γ'} : v τ -> dep_env v Γ' -> dep_env v (τ :: Γ')
.
Arguments dep_nil {_ _}.
Arguments dep_cons {_ _ _ _} _ _.

Fixpoint dep_lookup {A} {v : A -> Type} {Γ} (ρ : dep_env v Γ) (x : nat)
  : option {τ : A & v τ} :=
  match ρ with
  | dep_nil => None
  | dep_cons e ρ' =>
    match x with
    | O => Some (existT _ _ e)
    | S x' => dep_lookup ρ' x'
    end
  end.

Fixpoint dep_env_map {A} {v0 v1 : A -> Type} {Γ}
         (f : forall a, v0 a -> v1 a)
         (ρ : dep_env v0 Γ)
  : dep_env v1 Γ :=
  match ρ with
  | dep_nil => dep_nil
  | dep_cons e ρ' => dep_cons (f _ e) (dep_env_map f ρ')
  end.

Fixpoint dep_env_allT {A} {v : A -> Type} {Γ}
         (P : forall a, v a -> Type)
         (ρ : dep_env v Γ) : Type
  :=
    match ρ with
    | dep_nil => True
    | dep_cons e ρ' => P _ e ⨉ dep_env_allT P ρ'
    end.

Definition wt_env := dep_env val.

Fixpoint erase_wt_expr_env {Γ Δ} (ρ : dep_env (fun τ => expr Δ τ ObsNone) Γ)
  : (nat -> u_expr) :=
  match ρ with
  | dep_nil => ids
  | dep_cons e ρ' => erase e .: erase_wt_expr_env ρ'
  end.

Fixpoint erase_wt_env {Γ} (ρ : wt_env Γ) : nat -> u_expr :=
  match ρ with
  | dep_nil => ids
  | dep_cons e ρ' => erase e .: erase_wt_env ρ'
  end.

Lemma erase_envs_equiv {Γ} (ρ : wt_env Γ) :
  erase_wt_expr_env (dep_env_map (@expr_of_val) ρ) =
  erase_wt_env ρ.
Proof.
  induction ρ; cbn; auto.
  f_equal.
  auto.
Qed.

(* Definition subst_of_WT_Env {Γ} (ρ : WT_Env Γ) : nat -> Expr := *)
(*   sapp (downgrade_env ρ) ids. *)

(* Lemma subst_of_WT_Env_lookup {Γ x v} {ρ : WT_Env Γ} : *)
(*   (lookup ρ x = Some v) -> *)
(*   subst_of_WT_Env ρ x = v. *)
(* Proof. *)
(*   intros. *)
(*   unfold subst_of_WT_Env. *)
(*   destruct ρ as [ρ]. *)
(*   simpl in *. *)
(*   clear WT_Env_tc0. *)
(*   revert ρ H. *)
(*   induction x; intros. { *)
(*     destruct ρ; try discriminate. *)
(*     inversion H. *)
(*     autosubst. *)
(*   } { *)
(*     destruct ρ; try discriminate. *)
(*     apply IHx. *)
(*     auto. *)
(*   } *)
(* Qed. *)

Definition env_search {A Γ} {v : A -> Type} (ρ : dep_env v Γ) {x τ} :
  lookup Γ x = Some τ ->
  {e : v τ | dep_lookup ρ x = Some (existT v τ e)}.
Proof.
  intros.
  revert Γ ρ H.
  induction x; intros. {
    destruct Γ; inversion H; subst.
    dependent destruction ρ.
    eexists.
    reflexivity.
  } {
    destruct Γ; try solve [inversion H]; subst.
    dependent destruction ρ.
    cbn in *.
    exact (IHx _ _ H).
  }
Qed.

Lemma lookup_subst {Γ x τ v} (ρ : wt_env Γ) :
  dep_lookup ρ x = Some (existT val τ v) ->
  erase v = erase_wt_env ρ x.
Proof.
  revert Γ ρ.
  induction x; intros. {
    destruct ρ; inversion H; subst.
    dependent destruction H2.
    auto.
  } {
    destruct ρ; inversion H; subst.
    cbn.
    apply IHx.
    auto.
  }
Qed.

Lemma weaken_lookup {A} {Γ : Env A} {x τ Γw} :
  lookup Γ x = Some τ ->
  lookup (Γ ++ Γw) x = Some τ.
Proof.
  intros.
  revert Γ H.
  induction x; intros. {
    destruct Γ; inversion H.
    auto.
  } {
    destruct Γ; try discriminate H.
    simpl in *.
    apply IHx.
    auto.
  }
Qed.

Fixpoint weaken {Γ τ ϕ} (e : expr Γ τ ϕ) Γw : expr (Γ ++ Γw) τ ϕ :=
  match e with
  | e_real r => e_real r
  | e_var x H => e_var x (weaken_lookup H)
  | e_lam body => e_lam (weaken body Γw)
  | e_app ef ea => e_app (weaken ef Γw) (weaken ea Γw)
  | e_factor e => e_factor (weaken e Γw)
  | e_sample => e_sample
  | e_observe e0 e1 => e_observe (weaken e0 Γw) (weaken e1 Γw)
  | e_unop op e => e_unop op (weaken e Γw)
  | e_binop op Hϕ el er => e_binop op Hϕ (weaken el Γw) (weaken er Γw)
  | e_hide_observable e => e_hide_observable (weaken e Γw)
  end.

Lemma weaken_eq {Γ τ ϕ} (e : expr Γ τ ϕ) Γw :
  erase e = erase (weaken e Γw).
Proof.
  induction e; simpl; f_equal; auto.
Qed.

Lemma expr_ren {Γ τ ϕ} ξ (e : expr Γ τ ϕ) Δ :
  lookup Γ = ξ >>> lookup Δ ->
  {e' : expr Δ τ ϕ |
   erase e' = rename ξ (erase e)}.
Proof.
  revert ξ Δ.
  induction e; intros. {
    exists (e_real r).
    simpl.
    auto.
  } {
    simple refine (exist _ (e_var (ξ x) _) _); simpl; auto.
    rewrite <- H.
    rewrite H0.
    auto.
  } {
    assert (lookup (τa :: Γ) = upren ξ >>> lookup (τa :: Δ)). {
      extensionality x.
      destruct x; auto.
      simpl.
      rewrite H.
      auto.
    }
    destruct (IHe _ _ H0).
    exists (e_lam x).
    simpl.
    rewrite e0.
    auto.
  } {
    edestruct IHe1, IHe2; eauto.
    eexists (e_app _ _).
    simpl.
    rewrite e, e0.
    auto.
  } {
    edestruct IHe; eauto.
    eexists (e_factor _).
    simpl.
    rewrite e0.
    auto.
  } {
    exists e_sample; auto.
  } {
    edestruct IHe1, IHe2; eauto.
    eexists (e_observe _ _).
    simpl.
    rewrite e, e0.
    auto.
  } {
    edestruct IHe; eauto.
    eexists (e_unop op _).
    simpl.
    rewrite e0.
    auto.
  }{
    edestruct IHe1, IHe2; eauto.
    eexists (e_binop op Hϕ _ _).
    simpl.
    rewrite e, e0.
    auto.
  } {
    edestruct IHe; eauto.
    eexists (e_hide_observable _).
    simpl.
    rewrite e0.
    auto.
  }
Qed.

Lemma up_inj : Injective up.
  intros ? ? ?.
  assert (forall z, up x z = up y z). {
    rewrite H.
    auto.
  }
  extensionality z.
  specialize (H0 (S z)).
  unfold up in H0.
  simpl in H0.
  set (x z) in *.
  set (y z) in *.
  set (+1)%nat in *.
  assert (Injective v). {
    intros ? ? ?.
    subst v.
    inversion H; auto.
  }
  clearbody v u u0.
  revert u0 v H0 H1.
  clear.
  induction u; intros; destruct u0; inversion H0; f_equal; eauto. {
    eapply IHu; eauto.
    repeat intro.
    revert H1 H; clear; intros.
    compute in H.
    destruct x, y; auto; discriminate H.
  }
Qed.

Lemma up_expr_env {Γ Δ : Env Ty}
      (σ : dep_env (fun τ => expr Δ τ ObsNone) Γ)
      (τa : Ty)
  : { σ' : dep_env (fun τ => expr (τa :: Δ) τ ObsNone) (τa :: Γ) |
      forall x τ,
        lookup (τa :: Γ) x = Some τ ->
        erase_wt_expr_env σ' x = up (erase_wt_expr_env σ) x }.
Proof.
  simple refine (exist _ _ _); auto. {
    constructor. {
      apply (e_var O).
      auto.
    } {
      refine (dep_env_map _ σ).
      intros a e.
      apply (expr_ren S e).
      auto.
    }
  } {
    simpl.
    intros.
    revert Γ Δ σ H.
    destruct x; auto.
    induction x; intros. {
      simpl.
      destruct σ; inversion H; subst.
      simpl.
      destruct expr_ren.
      rewrite e0.
      auto.
    } {
      destruct σ; try discriminate H; simpl in *.
      rewrite IHx; auto.
    }
  }
Qed.

Lemma subst_only_matters_up_to_env {Γ τ ϕ} (e : expr Γ τ ϕ) σ0 σ1 :
  (forall x τ,
      lookup Γ x = Some τ ->
      σ0 x = σ1 x) ->
  (erase e).[σ0] = (erase e).[σ1].
Proof.
  revert σ0 σ1.
  induction e; simpl; intros; f_equal; eauto.

  apply IHe.
  intros.
  destruct x; auto.
  simpl in H0.
  specialize (H _ _ H0).
  unfold up.
  simpl.
  rewrite H.
  auto.
Qed.

Lemma ty_subst {Γ τ ϕ} (e : expr Γ τ ϕ) :
  forall Δ (ρ : dep_env (fun τ => expr Δ τ ObsNone) Γ),
    {e' : expr Δ τ ϕ |
     erase e' = (erase e).[erase_wt_expr_env ρ]}.
Proof.
  induction e; intros. {
    exists (e_real r).
    reflexivity.
  } {
    simpl.
    destruct (env_search ρ H).
    exists x0.
    revert Γ H ρ e.
    induction x; intros. {
      destruct ρ; inversion e; subst.
      auto.
    } {
      destruct ρ; inversion e; subst.
      simpl.
      apply IHx; auto.
    }
  } {
    destruct (up_expr_env ρ τa) as [ρ' Hρ'].
    destruct (IHe _ ρ').

    eexists (e_lam _).
    simpl.
    f_equal.
    rewrite e0.

    apply subst_only_matters_up_to_env.
    auto.
  } {
    edestruct IHe1, IHe2; auto.
    eexists (e_app _ _).
    simpl.
    rewrite e, e0.
    reflexivity.
  } {
    edestruct IHe; auto.
    exists (e_factor x).
    simpl.
    rewrite e0.
    reflexivity.
  } {
    exists e_sample.
    reflexivity.
  } {
    edestruct IHe1, IHe2; auto.
    exists (e_observe x x0).
    simpl.
    rewrite e, e0.
    reflexivity.
  } {
    edestruct IHe; auto.
    exists (e_unop op x).
    simpl.
    rewrite e0.
    reflexivity.
  } {
    edestruct IHe1, IHe2; auto.
    exists (e_binop op Hϕ x x0).
    simpl.
    rewrite e, e0.
    reflexivity.
  } {
    edestruct IHe; auto.
    exists (e_hide_observable x).
    simpl.
    rewrite e0.
    reflexivity.
  }
Qed.

Lemma close {Γ} (ρ : wt_env Γ) {τ ϕ} (e : expr Γ τ ϕ) :
  {e' : expr · τ ϕ |
   erase e' = (erase e).[erase_wt_env ρ]}.
Proof.
  rewrite <- erase_envs_equiv.
  apply ty_subst.
Qed.

Lemma close_nil (ρ : wt_env ·) {τ ϕ} (e : expr · τ ϕ) :
  proj1_sig (close ρ e) = e.
Proof.
  d_destruct ρ.
  elim_sig_exprs.
  elim_erase_eqs.
  trivial.
Qed.

Definition ty_subst1 {τa τr ϕ}
      (e : expr (τa :: ·) τr ϕ)
      (v : val τa) :
  { e' : expr · τr ϕ |
    erase e' = (erase e).[erase v /] }
  := ty_subst e · (dep_cons (v : expr _ _ _) dep_nil).

Reserved Notation "'EVAL' σ ⊢ e ⇓ v , w" (at level 69, e at level 99, no associativity).
Reserved Notation "'OBS_EVAL' σ ⊢ e ⇓ v , w" (at level 69, e at level 99, no associativity).
Inductive eval (σ : Entropy) : forall {τ ϕ} (e : expr · τ ϕ) (v : val τ) (w : R+), Type :=
| EPure {τ} (v : val τ) :
    (EVAL σ ⊢ v ⇓ v, 1)
| EApp {τa τr ϕf ϕa ϕ}
       {ef : expr · (τa ~~ ϕ ~> τr) ϕf}
       {ea : expr · τa ϕa}
       {body : expr (τa :: ·) τr ϕ}
       {va : val τa}
       {vr : val τr}
       {w0 w1 w2 : R+}
  : (EVAL (π 0 σ) ⊢ ef ⇓ (v_lam body), w0) ->
    (EVAL (π 1 σ) ⊢ ea ⇓ va, w1) ->
    (EVAL (π 2 σ) ⊢ proj1_sig (ty_subst1 body va) ⇓ vr, w2) ->
    (EVAL σ ⊢ e_app ef ea ⇓ vr, w0 * w1 * w2)
| EFactor {ϕ} {e : expr · ℝ ϕ} {r : R} {w : R+} {is_v} (rpos : (0 <= r)%R)
  : (EVAL σ ⊢ e ⇓ mk_val (e_real r) is_v, w) ->
    (EVAL σ ⊢ e_factor e ⇓ v_real r, finite r rpos * w)
| ESample
  : (EVAL σ ⊢ e_sample ⇓ v_real (proj1_sig (σ O)), 1)
| EObserve {ϕ0} {e0 : expr · ℝ ϕ0} {e1 : expr · ℝ ObsR} {v : val ℝ} {w0 w1 : R+}
  : (EVAL (π 0 σ) ⊢ e0 ⇓ v, w0) ->
    (OBS_EVAL (π 1 σ) ⊢ e1 ⇓ v, w1) ->
    (EVAL σ ⊢ e_observe e0 e1 ⇓ v, w0 * w1)
| EUnop {op : unop}
        {ϕ}
        {e0 : expr · ℝ ϕ}
        {r0 r : R}
        {is_v0}
        {w0 : R+}
  : (EVAL σ ⊢ e0 ⇓ mk_val (e_real r0) is_v0, w0) ->
    δ1 op r0 = Some r ->
    (EVAL σ ⊢ e_unop op e0 ⇓ v_real r, w0)
| EBinop {op : binop}
         {ϕ0 ϕ1 ϕ}
         {e0 : expr · ℝ ϕ0}
         {e1 : expr · ℝ ϕ1}
         {r0 r1 r : R}
         {is_v0 is_v1 Hϕ}
         {w0 w1 : R+}
  : (EVAL (π 0 σ) ⊢ e0 ⇓ mk_val (e_real r0) is_v0, w0) ->
    (EVAL (π 1 σ) ⊢ e1 ⇓ mk_val (e_real r1) is_v1, w1) ->
    δ2 op r0 r1 = Some r ->
    (EVAL σ ⊢ e_binop (ϕ := ϕ) op Hϕ e0 e1 ⇓ v_real r, w0 * w1)
| EHide {v w}
        {e : expr · ℝ ObsR}
  : (EVAL σ ⊢ e ⇓ v, w) ->
    (EVAL σ ⊢ e_hide_observable e ⇓ v, w)
with
(* should `val ℝ` be replaced with R here? *)
eval_obs (σ : Entropy) : forall (e : expr · ℝ ObsR) (v : val ℝ) (w : R+), Type :=
| OApp {τa ϕf ϕa}
       {ef : expr · (τa ~~ ObsR ~> ℝ) ϕf}
       {ea : expr · τa ϕa}
       {body : expr (τa :: ·) ℝ ObsR}
       {va : val τa}
       {vr : val ℝ}
       {w0 w1 w2 : R+}
  : (EVAL (π 0 σ) ⊢ ef ⇓ mk_val (e_lam body) I, w0) ->
    (EVAL (π 1 σ) ⊢ ea ⇓ va, w1) ->
    (OBS_EVAL (π 2 σ) ⊢ proj1_sig (ty_subst1 body va) ⇓ vr, w2) ->
    (OBS_EVAL σ ⊢ e_app ef ea ⇓ vr, w0 * w1 * w2)
| OUnop {op : unop}
        {e0 : expr · ℝ ObsR}
        {r0 r : R} {is_v0} {w0 : R+}
  : δ1_inv op r = Some r0 ->
    (OBS_EVAL σ ⊢ e0 ⇓ mk_val (e_real r0) is_v0, w0) ->
    (OBS_EVAL σ ⊢ e_unop op e0 ⇓ v_real r, w0 / ennr_abs (δ1_partial_deriv op r0))
| OBinop {op : binop}
         {ϕ0}
         {e0 : expr · ℝ ϕ0}
         {e1 : expr · ℝ ObsR}
         {r0 r1 r : R} {is_v0 is_v1 Hϕ} {w0 w1 : R+}
  : (EVAL (π 0 σ) ⊢ e0 ⇓ mk_val (e_real r0) is_v0, w0) ->
    δ2_inv op r0 r = Some r1 ->
    (OBS_EVAL (π 1 σ) ⊢ e1 ⇓ mk_val (e_real r1) is_v1, w1) ->
    (OBS_EVAL σ ⊢ e_binop op Hϕ e0 e1 ⇓ v_real r, w0 * w1 / ennr_abs (δ2_partial_deriv op r0 r1))
| OSample {r : R}
  : (0 <= r <= 1)%R ->
    (OBS_EVAL σ ⊢ e_sample ⇓ v_real r, 1)
where "'OBS_EVAL' σ ⊢ e ⇓ v , w" := (eval_obs σ e v w)
and "'EVAL' σ ⊢ e ⇓ v , w" := (eval σ e v w)
.

Lemma invert_eval_val {σ τ} {v v' : val τ} {w} :
  (EVAL σ ⊢ v ⇓ v', w) ->
  v = v' /\ w = 1.
Proof.
  intros.
  destruct τ;
    destruct_val v;
    destruct_val v';
    dependent destruction H;
    auto.
Qed.

Lemma u_expr_eq_dec (u0 u1 : u_expr) :
  {u0 = u1} + {u0 <> u1}.
Proof.
  repeat decide equality.
  apply Req_EM_T.
Qed.

Lemma expr_eq_dec {Γ τ ϕ} (e0 e1 : expr Γ τ ϕ) :
  {e0 = e1} + {e0 <> e1}.
Proof.
  destruct (u_expr_eq_dec (erase e0) (erase e1)). {
    left.
    elim_erase_eqs.
    auto.
  } {
    right.
    intro.
    subst.
    auto.
  }
Qed.