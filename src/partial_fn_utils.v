Require Import Coq.Reals.Reals.
Require Import Coq.Sets.Ensembles.

Section PartialBijections.
  Context
    {X Y : Type}
    (f : X -> option Y)
    (finv : Y -> option X).

  Definition partial_bijection : Prop :=
    forall x y, f x = Some y <-> finv y = Some x.

  Definition dom (x : X) : Prop :=
    match f x with
    | Some _ => True
    | None => False
    end.

  Definition im (y : Y) : Prop :=
    exists x, f x = Some y.
End PartialBijections.

Lemma partial_bijection_sym {X Y} (f : X -> option Y) g :
  partial_bijection f g -> partial_bijection g f.
Proof.
  firstorder.
Qed.

Lemma partial_bijection_full {X Y} (f : X -> option Y) g :
    partial_bijection f g ->
    dom g = im f.
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; intros y H0; hnf in *;
    remember (g y) as gy;
    destruct gy; try solve [trivial | contradiction].
  {
    exists x.
    apply H.
    auto.
  } {
    destruct H0.
    destruct (H x y).
    rewrite H1 in Heqgy; auto.
    discriminate.
  }
Qed.

Definition fromOption {A} (d : A) (opt : option A) : A :=
  match opt with
  | Some a' => a'
  | None => d
  end.

Definition partially_derivable (f : R -> option R) :=
  forall x r, f x <> None -> derivable_pt (fun x' => fromOption r (f x')) x.

Definition partially_derive (f : R -> option R) (pr : partially_derivable f) (x : R) : option R :=
  match f x as fx return f x = fx -> option R with
  | Some r => fun H => Some (proj1_sig (pr x R0 ltac:(rewrite H; discriminate)))
  | None => fun _ => None
  end eq_refl.