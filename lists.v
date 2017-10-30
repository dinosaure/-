Theorem surjective_pairing : forall (n m : nat), (n, m) = (fst (n, m), snd (n, m)).
Proof. reflexivity. Qed.

Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Theorem surjective_pairing' : forall (p : natprod), p = (fst p, snd p).
Proof.
  intros [n m].
  simpl.
  reflexivity.
Qed.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | pair x y => pair y x
  end.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros [n m].
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros [n m].
  simpl.
  reflexivity.
Qed.
