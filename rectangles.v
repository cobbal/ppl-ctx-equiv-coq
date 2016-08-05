Require Coq.Program.Tactics.

Inductive Ty :=
| R : Ty
| arrowT : Ty -> Ty -> Ty
| prodT : Ty -> Ty -> Ty
.

Axiom real : Type.
Axiom expr : Type.

Inductive Val :=
| v_real : real -> Val
| v_clo : list Val -> expr -> Val
| v_pair : Val -> Val -> Val
.


Notation "a ⨉ b" := (prodT a b) (at level 20).
Notation "a ~> b" := (arrowT a b) (at level 20).

Definition Event := Val -> Prop.
Axiom μ : list Val -> expr -> Event -> real.

Definition A_rel' (V_rel : Ty -> Val -> Val -> Type) (τ : Ty) (A : Event) :=
  forall v0 v1,
    V_rel τ v0 v1 ->
    (A v0 <-> A v1).

Definition E_rel'
           (V_rel : Ty -> Val -> Val -> Prop)
           (τ : Ty)
           (ρ1 : list Val)
           (e1 : expr)
           (ρ2 : list Val)
           (e2 : expr)
: Prop :=
  forall A,
    A_rel' V_rel τ A ->
    μ ρ1 e1 A = μ ρ2 e2 A
.

Fixpoint V_rel (τ : Ty) (v1 v2 : Val) : Prop :=
  match τ, v1, v2 with
  | R, v_real r1, v_real r2 => r1 = r2
  | τa ~> τr, v_clo ρ1 e1, v_clo ρ2 e2 =>
    forall va1 va2,
      V_rel τa va1 va2 ->
      E_rel' V_rel τr (va1 :: ρ1) e1 (va2 :: ρ2) e2
  | τl ⨉ τr, v_pair vl1 vr1, v_pair vl2 vr2 =>
    V_rel τl vl1 vl2 /\ V_rel τr vr1 vr2
  | _, _, _ => False
  end.

Definition E_rel := E_rel' V_rel.
Definition A_rel := A_rel' V_rel.

Definition eventProd (ea eb : Event) : Event :=
  fun ab =>
    match ab with
    | v_pair a b => ea a /\ eb b
    | _ => False
    end.

Lemma foo :
  forall Al Ar τl τr,
    A_rel τl Al ->
    A_rel τr Ar ->
    A_rel (τl ⨉ τr) (eventProd Al Ar).
Proof.
  intros.
  intros v1 v2.
  intros.
  induction v1, v2; unfold eventProd; try (split; intro; tauto).
  induction H1.

  split; (
    intro;
    induction H3;
    split; [pose proof H _ _ H1 | pose proof H0 _ _ H2];
      induction H5;
      intuition
    ).
Qed.

Lemma bar :
  forall Al Ar τl τr,
    A_rel (τl ⨉ τr) (eventProd Al Ar) ->
    A_rel τl Al.
Proof.
  intros.
Abort.