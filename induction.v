Require Export Basics.

Theorem plus_n_0 : forall n : nat, n = n + 0.
Proof.
  intros n.
  induction n as [| n' Sn'].
  - reflexivity. (* n = 0 *)
  - simpl. (* S n' = S n' + 0 -> S n' = S (n' + 0) *)
    rewrite <- Sn'. (* Sn' : n' = n' + 0, S n' = S (n' + 0) -> S n' = S n' *)
    reflexivity.
Qed.

Theorem minus_diag : forall n, minus n n = 0.
Proof.
  induction n as [| n' Sn'].
  - simpl. reflexivity.
  - simpl. rewrite -> Sn'. reflexivity.
Qed.

Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
  induction n as [| n' Sn' ].
  - reflexivity.
  - simpl. rewrite -> Sn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' Sn' ].
  - simpl. reflexivity.
  - simpl. rewrite -> Sn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' Sn' ].
  - simpl. rewrite <- plus_n_0. reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite <- Sn'. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' Sn' ].
  - simpl. reflexivity.
  - simpl. rewrite <- Sn'. reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  induction n as [| n' Sn' ].
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite <- Sn'. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  induction n as [| n' Sn' ].
  - simpl. reflexivity.
  - rewrite -> Sn'. simpl. rewrite -> negb_involutive. reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H : m + n = n + m).
  - rewrite -> plus_comm. reflexivity.
  - rewrite -> H. reflexivity.
Qed.
