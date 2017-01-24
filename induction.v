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

(* Temporary introduce even b as Require Export doesn't work for me *)
Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

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