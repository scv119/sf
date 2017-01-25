Add LoadPath "/Users/chenshen/src/sf/".

Require Export Basics.

Theorem plus_n_O_secondtry: forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [|n'].
  - reflexivity.
  - simpl.
Abort.


Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mult_0_r : forall n: nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + S(m).
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Lemma neg_neg_lemma : forall n : bool,
  n = negb (negb n).
Proof.
  intros [].
  - simpl. reflexivity.
  - simpl. reflexivity.
  Qed.


Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros [|m].
  - simpl. reflexivity.
  - simpl. induction m as [|m' IHm'].
    + simpl. reflexivity.
    + simpl. rewrite -> IHm'. rewrite <- neg_neg_lemma. reflexivity. Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_comm.
  assert (H: p + n = n + p).
  { rewrite plus_comm. reflexivity. }
  rewrite <- H.
  rewrite -> plus_assoc. reflexivity. Qed.

Theorem mult_0 : forall n : nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mult_comm_lemma: forall n m : nat,
  n * S m = n + n * m.
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_swap. reflexivity. Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m .
Proof.
  intros n m. destruct n as [|n'].
  - rewrite -> mult_0. simpl. reflexivity.
  - induction m as [|m' IHm'].
    + simpl. rewrite -> mult_0. reflexivity.
    + simpl. rewrite <- IHm'. simpl. rewrite -> plus_swap. rewrite mult_comm_lemma. reflexivity. Qed.

(* Need induction *)
Theorem leb_refl : forall n : nat,
  true = leb n n.
Proof. 
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

(* Simple *)
Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof. intros n. simpl. reflexivity. Qed.

(* Induction *)
Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n)(p + m) = true.
Proof.
  intros n m p H. induction p as [|p' IHp'].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHp'. reflexivity. Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_assoc. reflexivity. Qed.

Theorem mult_assoc: forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> mult_plus_distr_r. reflexivity. Qed.

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

