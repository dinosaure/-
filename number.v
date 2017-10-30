Module Nat.
  Inductive nat : Type :=
    | O : nat
    | S : nat -> nat
    .

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

  Definition minus_two (n : nat) : nat :=
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.

  Compute (minus_two (S (S (S (S O))))).

  Fixpoint even (n : nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => even n'
    end.

  Definition odd (n : nat) : bool := neg (even n).

  Example test_odd1 : odd (S O) = true.
  Proof. simpl. reflexivity. Qed.
  Example test_odd2 : odd (S (S (S (S O)))) = false.
  Proof. simpl. reflexivity. Qed.

  Fixpoint plus (u v : nat) : nat :=
    match u with
    | O => v
    | S u' => S (plus u' v)
    end.

  Example test_plus1 : plus O (S O) = (S O).
  Proof. simpl. reflexivity. Qed.
  Example test_plus2 : plus (S (S O)) (S (S O)) = (S (S (S (S O)))).
  Proof. simpl. reflexivity. Qed.

  Fixpoint mult (u v : nat) : nat :=
    match u with
    | O => O
    | S u' => plus v (mult u' v)
    end.

  Example test_mult1 : mult (S (S (S O))) (S (S (S O))) = (S (S (S (S (S (S (S (S (S O))))))))).
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus (u v : nat) : nat :=
    match u, v with
    | O, _ => O
    | S _, O => u
    | S u', S v' => minus u' v' (* a - b = (a - 1) - (b - 1) *)
    end.

  Fixpoint exp (base power : nat) : nat :=
    match power with
    | O => S O
    | S p => mult base (exp base p)
    end.

  Fixpoint fact (n : nat) : nat :=
    match n with
    | O => (S O)
    | S n' => mult n (fact n')
    end.

  Example test_fact1 : fact O = (S O).
  Proof. simpl. reflexivity. Qed.
  Example test_fact2 : fact (S (S (S O))) = (S (S (S (S (S (S O)))))).
  Proof. simpl. reflexivity. Qed.
  Example test_fact3 : fact (S (S (S (S (S O))))) = mult (S (S (S (S (S (S (S (S (S (S O)))))))))) (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))).
  Proof. simpl. reflexivity. Qed.

  Notation "x + y" := (plus x y)
                        (at level 50, left associativity)
                        : mynat_scope.
  Notation "x - y" := (minus x y)
                        (at level 50, left associativity)
                        : mynat_scope.
  Notation "x * y" := (mult x y)
                        (at level 40, left associativity)
                        : mynat_scope.

  Fixpoint eq (u v : nat) : bool :=
    match u with
    | O =>
      match v with
      | O => true
      | S _ => false
      end
    | S u' =>
      match v with
      | O => false
      | S v' => eq u' v' (* a = b = (a - 1) = (b - 1) *)
      end
    end.

  Fixpoint leq (u v : nat) : bool :=
    match u with
    | O => true
    | S u' =>
      match v with
      | O => false
      | S v' => leq u' v' (* a < b = (a - 1) < (b - 1) *)
      end
    end.

  Definition less (u v : nat) : bool :=
    neg (eq u v) && leq u v.

  Example test_less1 : less (S (S O)) (S (S O)) = false.
  Proof. simpl. reflexivity. Qed.
  Example test_less2 : less (S (S O)) (S (S (S (S O)))) = true.
  Proof. simpl. reflexivity. Qed.
  Example test_less3 : less (S (S (S (S O)))) (S (S O)) = false.
  Proof. simpl. reflexivity. Qed.

  Theorem plus_0_n : forall n : nat, plus O n = n.
  Proof.
    intros n. simpl. reflexivity. Qed.

  Theorem plus_1_l : forall n : nat, plus (S O) n = S n.
  Proof.
    intros n. reflexivity. Qed.

  Theorem mult_0_l : forall n : nat, mult O n = O.
  Proof.
    intros n. reflexivity. Qed.
End Nat.

Theorem plus_id : forall n m : nat,
  n = m -> n + n = m + m.
Proof. intros n m. intros H. rewrite -> H. reflexivity. Qed.

Theorem plus_id' : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. intros n m o. intros H. intros I. rewrite H. rewrite I. reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1 + n) = m * m.
Proof. intros n m. intros H. rewrite -> H. reflexivity. Qed.

Fixpoint beq_nat (u v : nat) :=
  match u, v with
  | O, O => true
  | O, S _ | S _, O => false
  | S u', S v' => beq_nat u' v'
  end.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n' ].
  - reflexivity. (* n = 0   => beq_nat (0 + 1) 0 = false *)
  - reflexivity. (* n = S n => beq_nat (S n + 1) 0 = false *)
Qed.

Definition negb (v : bool) :=
  match v with
  | true => false
  | false => true
  end.

Theorem negb_involutive : forall v : bool,
  negb (negb v) = v.
Proof.
  intros v.
  destruct v.
  - reflexivity. (* neg (neg true) = true *)
  - reflexivity. (* neg (neg false) = false *)
Qed.

Definition andb (u v : bool) :=
  match u with
  | true => v
  | false => false
  end.

Definition orb (u v : bool) :=
  match u with
  | true => true
  | false => v
  end.

Theorem andb_commutative : forall u v, andb u v = andb v u.
Proof.
  intros u v.
  destruct u.
  - destruct v.
    + reflexivity. (* u = true,  v = true  => and true true   = and true  true *)
    + reflexivity. (* u = true,  v = false => and true false  = and false true *)
  - destruct v.
    + reflexivity. (* u = false, v = true  => and false true  = and true  false *)
    + reflexivity. (* u = false, v = false => and false false = and false false *)
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros [| ].
  - reflexivity. (* beq_nat 0 (0 + 1) = false *)
  - reflexivity. (* beq_nat 0 (S n + 1) = false *)
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f F b.
  rewrite <- F. (* f (f b) -> f b *)
  rewrite <- F. (* f b -> b *)
  destruct b.
  - reflexivity. (* b = true, true = true *)
  - reflexivity. (* b = false, false = false *)
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = negb x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f F b.
  rewrite -> F. (* f (f b) -> negb (f b) *)
  rewrite -> F. (* negb (f v) -> negb (negb b) *)
  destruct b.
  - reflexivity. (* b = true, negb (negb true) = true *)
  - reflexivity. (* b = false, negb (negb false) = false *)
Qed.

Theorem andb_true_elim : forall u v : bool,
  andb u v = true -> v = true.
Proof.
  intros u v H.
  destruct u.
  - destruct v.
    + { rewrite <- H. reflexivity. }
    + { rewrite <- H. reflexivity. }
  - destruct v.
    + { rewrite <- H. reflexivity. }
    + { rewrite <- H. reflexivity. }
Qed.

Theorem orb_false_elim : forall u v : bool,
  orb u v = false -> u = false -> v = false.
Proof.
  intros u v H.
  destruct u.
  - destruct v.
    + { rewrite <- H. intros I. reflexivity. }
    + { rewrite <- H. intros I. reflexivity. }
  - { intros I. rewrite <- H. reflexivity. }
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
    (andb b c = orb b c) -> b = c.
Proof.
  intros u v.
  destruct u.
  - { simpl. (* andb true c = orb true c -> true = c |- c = true -> c = true |- c = c *)
      intros I. rewrite <- I. reflexivity. }
  - { simpl. (* andb false c = orb false c -> false = c |- false = c -> false = c |- c = c *)
      intros I. rewrite <- I. reflexivity. }
Qed.

Inductive bin : Type := | Zero : bin | Twice : bin -> bin | Succ : bin -> bin.

Definition incr (n : bin) : bin :=
  match n with
  | Zero => Succ Zero
  | Twice n' => Succ n'
  | Succ n' => Twice (Succ n')
  end.

Fixpoint bin_to_nat (n : bin) : nat :=
  match n with
  | Zero => O
  | Twice n' => (bin_to_nat n') + (bin_to_nat n')
  | Succ n' => (bin_to_nat n' * 2) + 1
  end.

Example test_0 : bin_to_nat (incr (incr (incr Zero))) = 3.
Proof. simpl. reflexivity. Qed.

