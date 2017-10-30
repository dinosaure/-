Inductive bool : Type :=
  | true : bool
  | false : bool
  .

Definition neg (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition and (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition or (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_or1 : (or true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_or2 : (or false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_or3 : (or false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_or4 : (or true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (and x y).
Notation "x || y" := (or x y).

Example test_or5 : false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nand (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => neg b2
  | false => true
  end.

Example test_nand1 : (nand true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nand2 : (nand false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nand3 : (nand false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nand4 : (nand true true) = false.
Proof. simpl. reflexivity. Qed.

Definition star (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
  match b1 with
  | true => b2 && b3
  | false => false
  end.

Example test_star1 : (star true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_star2 : (star false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_star3 : (star true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_star4 : (star true true false) = false.
Proof. simpl. reflexivity. Qed.
