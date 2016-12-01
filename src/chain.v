Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Import EqNotations.

(* A chain is like a list, but with dependent types that must link between
   consequetive pairs. If a list is a free monoid, maybe this is a free
   category? *)
Inductive chain {X} {P : X -> X -> Type} : X -> X -> Type :=
| chain_nil {A : X} : chain A A
| chain_cons {A B C : X} :
    P A B -> chain B C -> chain A C
.

Arguments chain {X} P _ _.
Infix ":::" := chain_cons (at level 60, right associativity).

Fixpoint chain_app {X} {P : X -> X -> Type} {A B C}
         (c : chain P A B) (c' : chain P B C) : chain P A C :=
  match c in (chain _ A' B') return (B = B' -> chain P A' C) with
  | chain_nil => fun HB => rew[fun B => chain P B C] HB in c'
  | x ::: xs =>
    fun HB =>
      x ::: chain_app xs (rew[fun B => chain P B C] HB in c')
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
  | x ::: xs => chain_snoc (chain_rev xs) x
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
    unfold chain_snoc.
    rewrite chain_app_assoc.
    reflexivity.
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

(* elimination predicate for a reverse chain, i.e. pretending it was defined by
   nil and snoc instead of nil and cons. *)
Lemma rev_chain_rect X (P : X -> X -> Type)
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

(* this could be expressed in terms of fold_right, but `cbn`s look nicer if it's
   spelled out as a fixpoint. *)
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

Lemma chain_to_list_app {X} {P : X -> X -> Type}
      {L}
      (f : forall A B, P A B -> L)
  : forall {A B C} (c : chain P A B) (c' : chain P B C),
    chain_to_list f (c +++ c') =
    app (chain_to_list f c) (chain_to_list f c').
Proof.
  intros.
  induction c; cbn; auto.
  rewrite IHc; auto.
Qed.

(* A bichain is just a chain on a product, but it makes a lot of things easier
   to spell it out . *)

Definition bicurry {A B C D E} (f : A -> B -> C -> D -> E)
  : (A * B) -> (C * D) -> E :=
  fun ab cd => f (fst ab) (snd ab) (fst cd) (snd cd).

Lemma dep_bicurry {A B C D} {E : A -> B -> C -> D -> Type}
      (f : forall A B C D, E A B C D)
  : forall (ab : A * B) (cd : C * D),
    bicurry E ab cd.
Proof.
  intros [? ?] [? ?].
  apply f.
Defined.

Definition bichain {X Y} (P : X -> Y -> X -> Y -> Type)
           (xA : X) (yA : Y) (xB : X) (yB : Y)
  : Type := @chain
              (X * Y)
              (bicurry P)
              (xA, yA)
              (xB, yB).
(* Inductive chain (X : Type) (P : X -> X -> Type) : X -> X -> Type := *)
(*     chain_nil : forall A : X, chain P A A *)
(*   | chain_cons : forall A B C : X, P A B -> chain P B C -> chain P A C *)

(* For chain: Argument X is implicit and maximally inserted *)
(* For chain_nil: Arguments X, P, A are implicit and maximally inserted *)
(* For chain_cons: Arguments X, P, A, B, C are implicit and maximally inserted *)
(* For chain: Argument scopes are [type_scope _ _ _] *)
(* For chain_nil: Argument scopes are [type_scope _ _] *)
(* For chain_cons: Argument scopes are [type_scope _ _ _ _ _ _] *)

Definition bichain_cons {X Y} {P : X -> Y -> X -> Y -> Type} {xA yA xB yB xC yC} :
  P xA yA xB yB -> bichain P xB yB xC yC -> bichain P xA yA xC yC
  := @chain_cons (X * Y) (bicurry P) (xA, yA) (xB, yB) (xC, yC).
(* Note to self: get more creative with notation *)
Infix ":2:" := bichain_cons (at level 60, right associativity).

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

Local Lemma surjective_pairing' {A B} (p : A * B) :
  p = (fst p, snd p).
Proof.
  destruct p.
  auto.
Defined.

Lemma bichain_rect X Y (P : X -> Y -> X -> Y -> Type)
      (motive : forall {xA xB yA yB}, bichain P xA xB yA yB -> Type)
      (case_nil : forall {x y}, @motive x y x y chain_nil)
      (case_cons : forall {xA yA xB yB xC yC}
                          (x : P xA yA xB yB)
                          (xs : bichain P xB yB xC yC),
          motive xs -> motive (x :2: xs)) :
  forall {xA yA xB yB} (c : bichain P xA yA xB yB), motive c.
Proof.
  intros.

  pose proof chain_rect (X * Y) (bicurry P).

  (* "transparent assert" from https://sympa.inria.fr/sympa/arc/coq-club/2015-10/msg00047.html *)
  simple refine (let motive' : forall A B : X * Y, chain (bicurry P) A B -> Type := _ in _). {
    intros.
    destruct_pairs.
    eapply motive.
    exact X1.
  }

  change (motive' _ _ c).
  apply X0; intros; destruct_pairs. {
    apply case_nil.
  } {
    apply case_cons; auto.
  }
Qed.

(* A trichain is just a chain on even more products!, this is getting stupid... *)

Local Notation "'π0' x" := (fst (fst x)) (at level 200).
Local Notation "'π1' x" := (snd (fst x)) (at level 200).
Local Notation "'π2' x" := (snd x) (at level 200).

Definition tricurry {A B C D E F G} (f : A -> B -> C -> D -> E -> F -> G)
  : (A * B * C) -> (D * E * F) -> G :=
  fun abc def => f (π0 abc) (π1 abc) (π2 abc) (π0 def) (π1 def) (π2 def).

Lemma dep_tricurry {A B C D E F} {G : A -> B -> C -> D -> E -> F -> Type}
      (f : forall A B C D E F, G A B C D E F)
  : forall (abc : A * B * C) (def : D * E * F),
    tricurry G abc def.
Proof.
  intros [[? ?] ?] [[? ?] ?].
  apply f.
Defined.
Print dep_tricurry.


Section trichain.
  Context {X Y Z : Type} {P : X -> Y -> Z -> X -> Y -> Z -> Type}.

  Definition trichain (xA : X) (yA : Y) (zA : Z) (xB : X) (yB : Y) (zB : Z)
    : Type := @chain
                (X * Y * Z)
                (tricurry P)
                (xA, yA, zA)
                (xB, yB, zB).

  Definition trichain_cons
             {xA yA zA xB yB zB xC yC zC} :
    P xA yA zA xB yB zB -> trichain xB yB zB xC yC zC -> trichain xA yA zA xC yC zC
    := @chain_cons (X * Y * Z) (tricurry P) (xA, yA, zA) (xB, yB, zB) (xC, yC, zC).
  (* Note to self: get more creative with notation *)
  Infix ":3:" := trichain_cons (at level 60, right associativity).

  Definition prod3_curry {A B C D} (f : A -> B -> C -> D) : A * B * C -> D :=
    fun abc =>
      f (π0 abc) (π1 abc) (π2 abc).

  Definition trichain_fold_right
             {F : X -> Y -> Z -> Type}
             (f : forall {xA yA zA xB yB zB}, P xA yA zA xB yB zB -> F xB yB zB -> F xA yA zA)
             {xB yB zB}
             (b : F xB yB zB)
             {xA : X} {yA : Y} {zA : Z}
             (c : trichain xA yA zA xB yB zB)
    : F xA yA zA.
  Proof.
    refine
      (@chain_fold_right
         (X * Y * Z)
         (tricurry P)
         (prod3_curry _)
         _
         (xB, yB, zB)
         b
         (xA, yA, zA)
         c).
    intros [[? ?] ?] [[? ?] ?] ? ?.
    exact (f _ _ _ _ _ _ X0 X1).
  Defined.

  Definition trichain_to_list
             {L : Type}
             (f : forall {xA yA zA xB yB zB}, P xA yA zA xB yB zB -> L)
             {xA yA zA xB yB zB} (c : trichain xA yA zA xB yB zB) : list L.
  Proof.
    refine (chain_to_list _ c).
    intros [[? ?] ?] [[? ?] ?] ?.
    eapply f; eauto.
  Defined.

  Local Lemma surjective_pairing'' {A B C} : forall (p : A * B * C),
      p = (π0 p, π1 p, π2 p).
  Proof.
    intros [[? ?] ?].
    auto.
  Defined.

  (* well this is ugly... *)
  Lemma trichain_rect
        (motive : forall {xA yA zA xB yB zB}, trichain xA yA zA xB yB zB -> Type)
        (case_nil : forall {x y z}, @motive x y z x y z chain_nil)
        (case_cons : forall {xA yA zA xB yB zB xC yC zC}
                            (x : P xA yA zA xB yB zB)
                            (xs : trichain xB yB zB xC yC zC),
            motive xs -> motive (x :3: xs)) :
    forall {xA yA zA xB yB zB} (c : trichain xA yA zA xB yB zB), motive c.
  Proof.
    intros ? ? ? ? ? ?.

    set (A := (xA, yA, zA)).
    set (B := (xB, yB, zB)).
    replace xA with (π0 A) by auto.
    replace yA with (π1 A) by auto.
    replace zA with (π2 A) by auto.
    replace xB with (π0 B) by auto.
    replace yB with (π1 B) by auto.
    replace zB with (π2 B) by auto.
    clearbody A B.
    clear xA yA zA xB yB zB.

    intros.

    unfold trichain in *.
    set (P' := tricurry P) in *.
    pose (m' := dep_tricurry motive).
    unfold tricurry in m'.

    change (m' (_, _, _) (_, _, _) c).
    assert (case_nil' : forall A, m' (π0 A, π1 A, π2 A)
                                     (π0 A, π1 A, π2 A) chain_nil). {
      intros [[? ?] ?].
      apply case_nil.
    }
    clear case_nil.
    assert (case_cons' : forall A B C x xs,
               m' (π0 B, π1 B, π2 B) (π0 C, π1 C, π2 C) xs ->
               m' (π0 A, π1 A, π2 A) (π0 C, π1 C, π2 C) (x ::: xs)).
    {
      intros [[? ?] ?] [[? ?] ?] [[? ?] ?] ? ? ?.
      apply case_cons.
      apply X0.
    }
    clearbody m'.
    clear case_cons motive.
    clearbody P'.
    clear P.

    pose (H := @surjective_pairing'' X Y Z).

    assert ({c' : chain P' A B &
                  m' A B (rew [fun A => chain P' A _] H A in
                             rew [chain P' A] H B in c') ->
                  m' (π0 A, π1 A, π2 A) (π0 B, π1 B, π2 B) c}).
    {
      destruct A as [[? ?] ?], B as [[? ?] ?].
      cbn in *.
      exists c.

      exact id.
    }

    destruct X0 as [c' H0].
    apply H0.
    clear H0 c.

    induction c'. {
      specialize (case_nil' A).
      destruct A as [[? ?] ?].
      cbn in *.
      assumption.
    } {
      specialize (case_cons' A B C).
      destruct A as [[? ?] ?], B as [[? ?] ?], C as [[? ?] ?].
      cbn in *.
      auto.
    }
  Qed.

  Definition trichain_snoc {xA yA zA xB yB zB xC yC zC} :
    trichain xA yA zA xB yB zB -> P xB yB zB xC yC zC -> trichain xA yA zA xC yC zC :=
    fun c x => c +++ x :3: chain_nil.

  Lemma rev_trichain_rect
        (motive : forall xA yA zA xB yB zB, trichain xA yA zA xB yB zB -> Type)
        (case_nil : forall xA yA zA, motive xA yA zA xA yA zA chain_nil)
        (case_snoc : forall xA yA zA xB yB zB xC yC zC
                            (x : P xB yB zB xC yC zC)
                            (c : trichain xA yA zA xB yB zB),
            motive xA yA zA xB yB zB c -> motive xA yA zA xC yC zC (trichain_snoc c x))
    : forall {xA yA zA xB yB zB} (c : trichain xA yA zA xB yB zB), motive xA yA zA xB yB zB c.
  Proof.
    intros.
    pose proof rev_chain_rect (X * Y * Z) (tricurry P).

    (* "transparent assert" from https://sympa.inria.fr/sympa/arc/coq-club/2015-10/msg00047.html *)
    simple refine (let motive' : forall A B : X * Y * Z, chain (tricurry P) A B -> Type := _ in _). {
      clear_except motive.
      intros.
      destruct_pairs.
      eapply motive.
      exact X0.
    }
    change (motive' _ _ c).
    apply X0; intros; destruct_pairs. {
      apply case_nil.
    } {
      apply case_snoc; auto.
    }
  Qed.
End trichain.

Arguments trichain {X Y Z} P.
Infix ":3:" := trichain_cons (at level 60, right associativity).
Arguments trichain_rect : clear implicits.
Arguments rev_trichain_rect : clear implicits.