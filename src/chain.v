Require Import Coq.Program.Basics.
Import EqNotations.

(** A chain (elsewhere called a type-aligned list) is like a list, but with
    dependent types that must link between consequetive pairs. If a list is a
    free monoid, maybe this is a free category? Anyway, it's a useful way to
    represent a typed context since it's composable on both the inside and the
    outside. *)
Inductive chain {X} {P : X -> X -> Type} : X -> X -> Type :=
| chain_nil {A : X} : chain A A
| chain_cons {A B C : X} :
    P A B -> chain B C -> chain A C
.

(** Most definitions and lemmas in this file will mirror that of [list] *)
Arguments chain {X} P _ _.
Infix ":::" := chain_cons (at level 60, right associativity).

Fixpoint chain_app {X} {P : X -> X -> Type} {A B C}
         (c : chain P A B) (c' : chain P B C) : chain P A C :=
  match c in (chain _ A' B') return (B = B' -> chain P A' C) with
  | chain_nil => fun HB => rew [fun B => chain P B C] HB in c'
  | x ::: xs =>
    fun HB =>
      x ::: chain_app xs (rew [fun B => chain P B C] HB in c')
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

Definition chain_fold_right {X} {P : X -> X -> Type}
         {F : X -> Type}
         (f : forall {A B : X}, P A B -> F B -> F A)
         {B : X}
         (b : F B)
  : forall {A : X}, chain P A B -> F A :=
  fix chain_fold_right {A} c :=
    match c in (chain _ A' B') return (B = B' -> F A') with
    | chain_nil => fun HB => rew [F] HB in b
    | x ::: c' =>
      fun HB =>
        f x (chain_fold_right (rew <- [chain P _] HB in c'))
    end eq_refl.

Definition chain_fold_left {X} {P : X -> X -> Type}
           {F : X -> Type}
           (f : forall {A B : X}, F A -> P A B -> F B)
  : forall {A B : X}, F A -> chain P A B -> F B :=
  fix chain_fold_left {A B} a c :=
    match c in (chain _ A' B') return (A = A' -> F B') with
    | chain_nil => fun HA => rew [F] HA in a
    | x ::: c' =>
      fun HA =>
        chain_fold_left (f a (rew <-[fun a => P a _] HA in x)) c'
    end eq_refl.

(** this could be expressed in terms of fold_right, but intermediate steps in
    computation look nicer if it's spelled out as a fixpoint. *)
Definition chain_to_list {X} {P : X -> X -> Type}
           {L : Type}
           (f : forall {A B : X}, P A B -> L)
  : forall {A B : X}, chain P A B -> list L :=
  fix chain_to_list {A B} c :=
    match c with
    | chain_nil => nil
    | x ::: c' =>
      cons (f x) (chain_to_list c')
    end.

(** A bichain is just a chain on a product, but it makes a lot of things easier
   to spell it out. *)

Definition bicurry {A B C D E} (f : A -> B -> C -> D -> E)
  : (A * B) -> (C * D) -> E :=
  fun ab cd => f (fst ab) (snd ab) (fst cd) (snd cd).

Definition bichain {X Y} (P : X -> Y -> X -> Y -> Type)
           (xA : X) (yA : Y) (xB : X) (yB : Y)
  : Type := @chain (X * Y) (bicurry P) (xA, yA) (xB, yB).

Definition bichain_cons {X Y} {P : X -> Y -> X -> Y -> Type} {xA yA xB yB xC yC} :
  P xA yA xB yB -> bichain P xB yB xC yC -> bichain P xA yA xC yC
  := @chain_cons (X * Y) (bicurry P) (xA, yA) (xB, yB) (xC, yC).
(* Note to self: get more creative with notation *)
Infix "::::" := bichain_cons (at level 60, right associativity).

Definition bichain_fold_right {X Y} {P : X -> Y -> X -> Y -> Type}
           {F : X -> Y -> Type}
           (f : forall {xA yA xB yB}, P xA yA xB yB -> F xB yB -> F xA yA)
           {xB yB}
           (b : F xB yB)
           {xA : X} {yA : Y}
           (c : bichain P xA yA xB yB)
  : F xA yA.
Proof.
  refine
    (@chain_fold_right
       (X * Y)
       (bicurry P)
       (prod_curry F)
       _
       (xB, yB)
       b
       (xA, yA)
       c).
  intros [? ?] [? ?] ? ?.
  exact (f _ _ _ _ X0 X1).
Defined.

Definition bichain_to_list {X Y} {P : X -> Y -> X -> Y -> Type}
         {L : Type}
         (f : forall {xA yA xB yB}, P xA yA xB yB -> L)
         {xA yA xB yB} (c : bichain P xA yA xB yB) : list L.
Proof.
  refine (chain_to_list _ c).
  intros [? ?] [? ?] ?.
  eapply f; eauto.
Defined.

Lemma bichain_rect X Y (P : X -> Y -> X -> Y -> Type)
      (motive : forall {xA xB yA yB}, bichain P xA xB yA yB -> Type)
      (case_nil : forall {x y}, @motive x y x y chain_nil)
      (case_cons : forall {xA yA xB yB xC yC}
                          (x : P xA yA xB yB)
                          (xs : bichain P xB yB xC yC),
          motive xs -> motive (x :::: xs)) :
  forall {xA yA xB yB} (c : bichain P xA yA xB yB), motive c.
Proof.
  intros.

  (* "transparent assert" from https://sympa.inria.fr/sympa/arc/coq-club/2015-10/msg00047.html *)
  simple refine (let motive' : forall A B : X * Y, chain (bicurry P) A B -> Type := _ in _). {
    intros [? ?] [? ?].
    apply motive.
  }

  change (motive' _ _ c).
  apply (chain_rect (X * Y) (bicurry P));
    subst motive';
    repeat intros [? ?];
    eauto.
Qed.