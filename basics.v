Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.


Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) :bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1: bool) (b2:bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1: bool) (b2:bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Infix "&&" := andb.
Infix "||" := orb.

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1: bool) (b2:bool) : bool :=
  match b1, b2 with
    | true, true => false
    | _, _ => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1: bool) (b2:bool) (b3:bool) : bool :=
  match b1, b2, b3 with
    | true, true, true => true
    | _, _, _ => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Module Playground1.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with 
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).

Compute (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_oddb2: oddb 4 =  false.
Proof. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n: nat) (m: nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with 
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_multi: (mult 3 3) = 9.
Proof. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat := 
  match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
  end.
End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S n => mult base (exp base n)
  end.

(* Exc factorial *)
Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
  (at level 50, left associativity)
  : nat_scope.

Notation "x - y" := (minus x y)
  (at level 50, left associativity)
  : nat_scope.

Notation "x * y" := (mult x y)
  (at level 40, left associativity)
  : nat_scope.

Check ((0 + 1) + 1).
Example test_notation: ((0 + 1) + 1) = 2.
Proof. simpl. reflexivity. Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
   | O => match m with
            | O => true
            | _ => false
          end
   | S n' => match m with
              | O => false
              | S m' => beq_nat n' m'
             end
  end.

Fixpoint leb (n m: nat): bool := 
  match n with
    | O => true
    | S n' =>
      match m with
        | O => false
        | S m' => leb n' m'
      end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Exc blt_nat *)
Definition blt_nat (n m: nat) : bool :=
  match (beq_nat n m) with
    | true => false
    | false => leb n m
  end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.