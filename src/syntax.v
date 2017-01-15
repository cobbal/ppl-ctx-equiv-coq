Require Import Coq.Reals.Reals.
Require Export Coq.Lists.List.

Require Export Autosubst.Autosubst.

Require Import utils.
Require Export entropy.


Local Open Scope ennr.

(** * Types *)

(** Types for our language are traditional real numbers (positive and negative,
    no infinity) and arrows. *)
Inductive Ty :=
| ℝ : Ty
| Arrow : Ty -> Ty -> Ty
.
Notation "x ~> y" := (Arrow x y) (at level 69, right associativity).

Lemma ty_eq_dec : forall (τ τ' : Ty), {τ = τ'} + {τ <> τ'}.
Proof.
  decide equality.
Defined.

(** Environments are De Bruijn indexed lists. While doing lookup in a list is
    slightly annoying and slightly mismatched with autosubst, the finiteness
    allows for things to be unique and decidable. *)
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

(** * Expressions

    While Autosubst (https://www.ps.uni-saarland.de/autosubst/) brings light and
    joy into the miserable world of doing substitutions, it has some issues that
    affect our representation of terms.

    We define expressions using a GADT so that all terms are well typed.
    However, autosubst is unable to either derive instances (not that much of a
    problem) or reason about substitutions (big problem) of these terms.

    We work around this by also defining a mostly type-erased version of the
    terms for autosubst to work with. The type erasure is done carefully (i.e.
    we keep the annotations on ambiguous terms (i.e. lambda)) so that the
    erasure is injective. This means that whenever autosubst can demonstrate an
    equality between to erased terms we can leverage the injectivity to get an
    equality between fully typed terms.

    ---- *)

(** First, the well-typed terms: *)
Inductive expr (Γ : Env Ty) : Ty -> Type :=
| e_real (r : R) : expr Γ ℝ
| e_var {τ : Ty} (x : var)
        (H : lookup Γ x = Some τ)
  : expr Γ τ
| e_lam {τa τr}
        (body : expr (τa :: Γ) τr)
  : expr Γ (τa ~> τr)
| e_app {τa τr}
        (ef : expr Γ (τa ~> τr))
        (ea : expr Γ τa)
  : expr Γ τr
| e_factor (e : expr Γ ℝ)
  : expr Γ ℝ
| e_sample
  : expr Γ ℝ
| e_plus (el : expr Γ ℝ)
         (er : expr Γ ℝ)
  : expr Γ ℝ.

Arguments e_real {Γ} r.
Arguments e_var {Γ τ} x H.
Arguments e_lam {Γ τa τr} body.
Arguments e_app {Γ τa τr} ef ea.
Arguments e_factor {Γ} e.
Arguments e_sample {Γ}.
Arguments e_plus {Γ} el er.

(** Now, the erased terms: (u stands for untyped) *)
Inductive u_expr :=
| u_app : u_expr -> u_expr -> u_expr
| u_factor : u_expr -> u_expr
| u_sample : u_expr
| u_plus : u_expr -> u_expr -> u_expr
| u_real : R -> u_expr
| u_lam : Ty -> {bind u_expr} -> u_expr
| u_var : var -> u_expr
.

Instance Ids_u_expr : Ids u_expr. derive. Defined.
Instance Rename_u_expr : Rename u_expr. derive. Defined.
Instance Subst_u_expr : Subst u_expr. derive. Defined.
Instance SubstLemmas_u_expr : SubstLemmas u_expr. derive. Defined.

Fixpoint erase {Γ τ} (e : expr Γ τ) : u_expr :=
  match e with
  | e_real r => u_real r
  | e_var x _ => u_var x
  | @e_lam _ τa τr body => u_lam τa (erase body)
  | e_app ef ea => u_app (erase ef) (erase ea)
  | e_factor e => u_factor (erase e)
  | e_sample => u_sample
  | e_plus el er => u_plus (erase el) (erase er)
  end.
Coercion erase' {Γ τ} : expr Γ τ -> u_expr := erase.
Arguments erase' / {_ _} _.

(** The first step towards proving injectivity of [erase] is uniqueness of
    typing for an erased term. *)
Lemma expr_type_unique {Γ τ0 τ1} (e0 : expr Γ τ0) (e1 : expr Γ τ1) :
  erase e0 = erase e1 ->
  τ0 = τ1.
Proof.
  intros Heq.
  revert τ1 e1 Heq.
  dependent induction e0; intros;
    dep_destruct (e1, Heq);
    auto.
  {
    rewrite H0 in H.
    inject H.
    reflexivity.
  } {
    rewrite (IHe0 _ _ x).
    reflexivity.
  } {
    specialize (IHe0_1 _ _ x).
    inject IHe0_1.
    reflexivity.
  }
Qed.

Require Import FinFun.
Lemma erase_injective Γ τ : Injective (@erase Γ τ).
Proof.
  intro x.
  dependent induction x;
    intros y Hxy;
    dep_destruct (y, Hxy);
    auto.
  {
    f_equal.
    apply UIP_dec.
    decide equality.
    apply ty_eq_dec.
  } {
    f_equal.
    apply IHx; auto.
  } {
    pose proof expr_type_unique _ _ x.
    inject H.
    erewrite IHx1, IHx2; auto.
  } {
    erewrite IHx; auto.
  } {
    erewrite IHx1, IHx2; auto.
  }
Qed.
Arguments erase_injective {_ _ _ _} _.


(** *** Tactics

    Some tactics useful for making use of equalities between erased expressions.
    *)

Ltac inject_erase_directly :=
  match goal with
  | [ H : erase ?x = erase ?y |- _ ] =>
    apply erase_injective in H;
    try subst x
  end.

Ltac match_erase_eqs :=
  let H := fresh "H" in
  let H' := fresh "H" in
  match goal with
  | [H0 : erase ?x = ?s, H1 : erase ?y = ?s |- _ ] =>
    pose proof (eq_trans H0 (eq_sym H1)) as H;
    let z := type of y in
    match type of x with
    | z => idtac
    | expr · ?τ =>
      pose proof (expr_type_unique _ _ H) as H';
      (subst τ || dep_destruct H')
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

(** dep_destruct is often slow, do don't use unless we need *)
(* TODO: speed up even more for exprs *)
Ltac expr_destruct e :=
  match type of e with
  | expr _ (_ ~> _) => dep_destruct e
  | expr _ ℝ => dep_destruct e
  | expr _ _ => destruct e
  end.

Ltac inject_erased :=
  let go e H :=
      expr_destruct e; inject H
  in match goal with
     | [ H : erase ?e = u_app _ _ |- _ ] => go e H
     | [ H : erase ?e = u_factor _ |- _ ] => go e H
     | [ H : erase ?e = u_sample |- _ ] => go e H
     | [ H : erase ?e = u_plus _ _ |- _ ] => go e H
     | [ H : erase ?e = u_real _ |- _ ] => go e H
     | [ H : erase ?e = u_lam _ _ |- _ ] => go e H
     | [ H : erase ?e = u_var _ |- _ ] => go e H
     | [ H : erase ?e = ids _ |- _ ] => go e H
     end.

(** [elim_erase_eqs]'s main objective is to eliminate hypothesis of the form
    [erase e = ...] *)
Ltac elim_erase_eqs :=
  progress repeat (subst_erase_eq
                   || inject_erase_directly
                   || match_erase_eqs
                   || inject_erased);
  clear_dups.

(** * Values

    While it would be nice to define values and exprs as mutually inductive
    types, autosubst can't handle mutual induction at the moment. Instead,
    values are defined as a subset type of expressions. For convenience, a
    coercion to expressions is defined. *)

Definition is_val (e : u_expr) : Prop :=
  match e with
  | u_real _ | u_lam _ _ => True
  | _ => False
  end.

Inductive val τ :=
  mk_val (e : expr · τ) (H : is_val e).
Arguments mk_val {τ} e H.
Coercion expr_of_val {τ} : val τ -> expr · τ :=
  fun v => let (e, _) := v in e.

(** proof irrelevance for [is_val], which also nicely means that coercion from a
    value to an expression is reversible. *)
Lemma is_val_unique {e : u_expr} (iv0 iv1 : is_val e) :
  iv0 = iv1.
Proof.
  destruct e; try contradiction; destruct iv0, iv1; auto.
Qed.

Lemma val_eq {τ} {v0 v1 : val τ} :
  v0 = v1 :> (expr · τ) ->
  v0 = v1 :> (val τ).
Proof.
  intros.
  destruct v0, v1.
  cbn in *.
  subst.

  f_equal.
  apply is_val_unique.
Qed.

(** the constructors for values I wish I had *)
Definition v_real r : val ℝ :=
  mk_val (e_real r) I.

Definition v_lam {τa τr} body : val (τa ~> τr) :=
  mk_val (e_lam body) I.

(** If a rewrite or other tactic is expecting a value, but sees an expression it
    will refuse to work. These two lemmas can be used to help the process along.
    *)
Definition rewrite_v_real r : e_real r = v_real r := eq_refl.
Definition rewrite_v_lam {τa τr} body : e_lam body = @v_lam τa τr body := eq_refl.

(** specialize destruction principles for values *)
Definition val_arrow_rect {τa τr}
           (P : val (τa ~> τr) -> Type)
           (case_lam : forall body, P (v_lam body)) :
  forall v, P v.
Proof.
  intros [v Hv].
  dependent destruction v; try contradiction Hv.
  destruct Hv.
  apply case_lam.
Qed.

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
Qed.

Lemma wt_val_rect {τ}
      (P : val τ -> Type)
      (case_real :
         forall r (τeq : ℝ = τ),
           P (rew τeq in v_real r))
      (case_lam :
         forall τa τr
                (τeq : (τa ~> τr) = τ)
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
    exact (case_lam _ _ eq_refl body).
  }
Qed.

Ltac destruct_val wt_v :=
  match (type of wt_v) with
  | val ℝ =>
    destruct wt_v using val_real_rect
  | val (?τa ~> ?τr) =>
    destruct wt_v using val_arrow_rect
  | val ?τ =>
    destruct wt_v using wt_val_rect
  end.

(** Quite often we will with a goal containing a [mk_val e False] hidden
    somewhere inside it. The tactic [absurd_val] hunts for that [False] in
    common places and contradicts it. *)

Lemma for_absurd_val {τ} {v : val τ} {e : expr · τ} :
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

(** * Using [sig] to program by tactics *)

(** As types get more dependent and pattern matching in Gallina becomes more
    challenging, we will make use of an idiom to define functions. If we want to
    define a function of type [A -> B], instead of defining it directly, we will
    opaquely define a function of the form [A -> {b : B | P b}] using tactics.

    The idea is to put all the information needed about the internals into [P]
    so that you can eliminate calls to the function (wich now look like
    [proj1_sig (f x)]) using [destruct (f x)] and rewriting insead of standard
    computation.

    The tactic [elim_sig_exprs] attempts to do exactly that destruction on
    results of type [expr]. *)
Ltac elim_sig_exprs :=
  let doit Γ τ pair stac :=
      (let e := fresh "e" in
       let He := fresh "H" e in
       destruct pair as [e He];
       stac;
       asimpl in He) in
  progress repeat
           match goal with
           | [ H : context [ @proj1_sig (expr ?Γ ?τ) _ ?pair ] |- _ ] =>
             doit Γ τ pair ltac:(simpl in H)
           | [ |- context [ @proj1_sig (expr ?Γ ?τ) _ ?pair ] ] =>
             doit Γ τ pair ltac:(simpl)
           end.


(** * Substitution

    Thanks to autosubst, substitution has been easily defined on erased terms.
    The goal now is to define substitution on well-typed terms. The process of
    defining it will be what is often called "proving a substitution lemma".

    {TODO: is that the right wording?} *)

(** First, we are going to need environments of well-typed terms. These will
    essentially be dependent lists. *)
Inductive dep_list {A} (v : A -> Type) : Env A -> Type :=
| dep_nil : dep_list v ·
| dep_cons {τ Γ'} : v τ -> dep_list v Γ' -> dep_list v (τ :: Γ')
.
Arguments dep_nil {_ _}.
Arguments dep_cons {_ _ _ _} _ _.

Fixpoint dep_lookup {A} {v : A -> Type} {Γ} (ρ : dep_list v Γ) (x : nat)
  : option {τ : A & v τ} :=
  match ρ with
  | dep_nil => None
  | dep_cons e ρ' =>
    match x with
    | O => Some (existT _ _ e)
    | S x' => dep_lookup ρ' x'
    end
  end.

Fixpoint dep_map {A} {v0 v1 : A -> Type} {Γ}
         (f : forall a, v0 a -> v1 a)
         (ρ : dep_list v0 Γ)
  : dep_list v1 Γ :=
  match ρ with
  | dep_nil => dep_nil
  | dep_cons e ρ' => dep_cons (f _ e) (dep_map f ρ')
  end.

Fixpoint dep_env_allT {A} {v : A -> Type} {Γ}
         (P : forall a, v a -> Type)
         (ρ : dep_list v Γ) : Type
  :=
    match ρ with
    | dep_nil => True
    | dep_cons e ρ' => P _ e * dep_env_allT P ρ'
    end.

(** Although in the end we only care about environments of closed values, for
    the intermediate stages of substitution we will need to work with
    environments of open terms as well.

    We will lift the erase function over environments, but we will do it as a
    separate function for open expressions vs values. The reason for this is to
    keep the casts between [val] and [expr ·] at cases better suited for
    computation. *)
Fixpoint erase_wt_expr_env {Γ Δ} (ρ : dep_list (expr Δ) Γ)
  : nat -> u_expr :=
  match ρ with
  | dep_nil => ids
  | dep_cons e ρ' => erase e .: erase_wt_expr_env ρ'
  end.

Definition wt_env := dep_list val.

Fixpoint erase_wt_env {Γ} (ρ : wt_env Γ) : nat -> u_expr :=
  match ρ with
  | dep_nil => ids
  | dep_cons e ρ' => erase e .: erase_wt_env ρ'
  end.

Lemma erase_envs_equiv {Γ} (ρ : wt_env Γ) :
  erase_wt_expr_env (dep_map (@expr_of_val) ρ) =
  erase_wt_env ρ.
Proof.
  induction ρ; auto.
  cbn.
  f_equal.
  auto.
Qed.

(** A downside to the list representation of environments is that doing lookup
    from a dependent list is awkward. *)
Lemma env_search {A Γ} {v : A -> Type} (ρ : dep_list v Γ) {x τ} :
  lookup Γ x = Some τ ->
  {e : v τ | dep_lookup ρ x = Some (existT v τ e)}.
Proof.
  intros.
  revert Γ ρ H.
  induction x; intros. {
    destruct Γ; inject H.
    dep_destruct ρ.
    eexists.
    reflexivity.
  } {
    destruct Γ; [discriminate |].
    dep_destruct ρ.
    simpl in *.
    exact (IHx _ _ H).
  }
Qed.

Lemma env_search_subst {Γ} (ρ : wt_env Γ) {x τ} :
  lookup Γ x = Some τ ->
  {v : val τ | erase v = erase_wt_env ρ x}.
Proof.
  intros.
  revert Γ ρ H.
  induction x; intros. {
    destruct Γ; inject H.
    dep_destruct ρ.
    eexists.
    reflexivity.
  } {
    destruct Γ; [discriminate |].
    dep_destruct ρ.
    simpl in *.
    exact (IHx _ _ H).
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

Fixpoint weaken {Γ τ} (e : expr Γ τ) Γw : expr (Γ ++ Γw) τ :=
  match e with
  | e_real r => e_real r
  | e_var x H => e_var x (weaken_lookup H)
  | e_lam body => e_lam (weaken body Γw)
  | e_app ef ea => e_app (weaken ef Γw) (weaken ea Γw)
  | e_factor e => e_factor (weaken e Γw)
  | e_sample => e_sample
  | e_plus el er => e_plus (weaken el Γw) (weaken er Γw)
  end.

(** The definition of typed substitution borrows from
    https://www.ps.uni-saarland.de/autosubst/doc/Plain.Demo.html *)

(** A combination of weakening and renaming preserves types *)
Lemma expr_ren {Γ τ} ξ (e : expr Γ τ) Δ :
  lookup Γ = ξ >>> lookup Δ ->
  {e' : expr Δ τ |
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
    eexists (e_plus _ _).
    simpl.
    rewrite e, e0.
    auto.
  }
Qed.

(** lift's autosubst's untyped [up] function to well-typed environments *)
Lemma up_expr_env {Γ Δ : Env Ty}
      (σ : dep_list (expr Δ) Γ)
      (τa : Ty)
  : { σ' : dep_list (expr (τa :: Δ)) (τa :: Γ) |
      forall x τ,
        lookup (τa :: Γ) x = Some τ ->
        erase_wt_expr_env σ' x = up (erase_wt_expr_env σ) x }.
Proof.
  simple refine (exist _ _ _); auto. {
    constructor. {
      apply (e_var O).
      auto.
    } {
      refine (dep_map _ σ).
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

(** Autosubst works with infinite substitution environments, but we never want
    to (and never have to) deal with the parts of the substitution that lie
    outside Γ. *)
Lemma subst_only_matters_up_to_env {Γ τ} (e : expr Γ τ) σ0 σ1 :
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

(** Finally we are armed with enough lemmas to define type-preserving
    substitution. *)
Lemma ty_subst {Γ τ} (e : expr Γ τ) :
  forall Δ (ρ : dep_list (expr Δ) Γ),
    {e' : expr Δ τ |
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
    destruct (up_expr_env ρ τa).
    destruct (IHe _ x).

    eexists (e_lam _).
    simpl.
    f_equal.
    rewrite e1.

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
    exists (e_plus x x0).
    simpl.
    rewrite e, e0.
    reflexivity.
  }
Qed.

Lemma close {Γ} (ρ : wt_env Γ) {τ} (e : expr Γ τ) :
  {e' : expr · τ |
   erase e' = (erase e).[erase_wt_env ρ]}.
Proof.
  rewrite <- erase_envs_equiv.
  apply ty_subst.
Qed.

Lemma close_nil (ρ : wt_env ·) {τ} (e : expr · τ) :
  proj1_sig (close ρ e) = e.
Proof.
  dep_destruct ρ.
  elim_sig_exprs.
  elim_erase_eqs.
  reflexivity.
Qed.

(** Since most day-to-day substitution is done by β, it's nice to have a small
    helper function to substitute exactly one value into a lambda body. *)
Definition ty_subst1 {τa τr}
      (e : expr (τa :: ·) τr)
      (v : val τa) :
  { e' : expr · τr |
    erase e' = (erase e).[erase v /] }
  := ty_subst e · (dep_cons (v : expr · τa) dep_nil).

(** * Evaluation *)

(** Evaluation is defined as a big-step relation. While it would have been nicer
    to instead define it as a partial function so that it's determinism is more
    obvious, the complicated recursion done by application means that
    determinism is instead done by logical relation in a more difficult manner.
    (See [eval_dec] in determinism.v) *)
Reserved Notation "'EVAL' σ ⊢ e ⇓ v , w" (at level 69, e at level 99, no associativity).
Inductive eval (σ : Entropy) : forall {τ} (e : expr · τ) (v : val τ) (w : R+), Type :=
| EVAL_val {τ} (v : val τ) :
    (EVAL σ ⊢ v ⇓ v, 1)
| EVAL_app {τa τr}
       {ef : expr · (τa ~> τr)}
       {ea : expr · τa}
       {body : expr (τa :: ·) τr}
       {va : val τa}
       {vr : val τr}
       {w0 w1 w2 : R+}
  : (EVAL (π 0 σ) ⊢ ef ⇓ mk_val (e_lam body) I, w0) ->
    (EVAL (π 1 σ) ⊢ ea ⇓ va, w1) ->
    (EVAL (π 2 σ) ⊢ proj1_sig (ty_subst1 body va) ⇓ vr, w2) ->
    (EVAL σ ⊢ e_app ef ea ⇓ vr, w0 * w1 * w2)
| EVAL_factor {e : expr · ℝ} {r : R} {w : R+} {is_v} (rpos : (0 <= r)%R)
  : (EVAL σ ⊢ e ⇓ mk_val (e_real r) is_v, w) ->
    (EVAL σ ⊢ e_factor e ⇓ v_real r, finite r rpos * w)
| EVAL_sample
  : (EVAL σ ⊢ e_sample ⇓ v_real (proj1_sig (σ O)), 1)
| EVAL_plus {e0 e1 : expr · ℝ} {r0 r1 : R} {is_v0 is_v1} {w0 w1 : R+}
  : (EVAL (π 0 σ) ⊢ e0 ⇓ mk_val (e_real r0) is_v0, w0) ->
    (EVAL (π 1 σ) ⊢ e1 ⇓ mk_val (e_real r1) is_v1, w1) ->
    (EVAL σ ⊢ e_plus e0 e1 ⇓ v_real (r0 + r1), w0 * w1)
where "'EVAL' σ ⊢ e ⇓ v , w" := (@eval σ _ e v w)
.

(** Misc lemmas *)

(** [inversion] has a hard time recognizing that [EVAL_val] is the only
    constructor that evaluates a value, so we use lemma instead. *)
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

(** Equality of expressions is decidable. Currently unused, but a nice tool to
    have for feeding to UIP_dec. *)
Lemma u_expr_eq_dec (u0 u1 : u_expr) :
  {u0 = u1} + {u0 <> u1}.
Proof.
  decide equality. {
    apply Req_EM_T.
  } {
    decide equality.
  } {
    decide equality.
  }
Qed.

(** The GADTs in [expr] are too much for the [decide equality] tactic.
    Fortunately, the hard work of converting it to a GADT-less version has
    already been done in erase_injective. *)
Lemma expr_eq_dec {Γ τ} (e0 e1 : expr Γ τ) :
  {e0 = e1} + {e0 <> e1}.
Proof.
  destruct (u_expr_eq_dec (erase e0) (erase e1)). {
    left.
    exact (erase_injective e).
  } {
    right.
    contradict n.
    subst.
    auto.
  }
Qed.