Add LoadPath "/Users/chenshen/src/sf/".
Require Export Logic.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).


Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : forall n, wrong_ev n -> wrong_ev (S (S n)).
(* ===> Error: A parameter of an inductive type n is not
        allowed to be used as a bound variable in the type
        of its constructor. *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn'.
Qed.


Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros [ | [ | n' ] ].
  - simpl. intros _. apply ev_0.
  - simpl. intros _. apply ev_0.
  - simpl.
Abort.


Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion  E as [|n' E'].
  - simpl. apply ev_0.
  - simpl. apply E'.
Qed.

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct  E as [|n' E'].
  - simpl. apply ev_0.
  - simpl. apply E'.
Qed.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  destruct E as [|n' E'].
Abort.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [|n' E'].
  apply E'.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H. inversion H. inversion H1. inversion H3.
Qed.

Lemma ev_even : forall n, 
  ev n -> exists k, n = double k.
Proof.
  intros n E. inversion E as [| n' E'].
  - exists 0. reflexivity.
Abort.

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E. 
  induction E as [|n' E' IH].
  - exists 0. reflexivity.
  - destruct IH as [k' IH'].
    exists (S k'). rewrite IH'. reflexivity.
Qed.

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.


Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m E1 E2.
  induction E1 as [|n' E1' IHE1'].
  - simpl. apply E2.
  - rewrite plus_comm. SearchAbout plus. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. apply ev_SS. rewrite plus_comm. apply IHE1'.
Qed.

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
 intros n. split.
 - intros E. induction E.
  + apply ev_0.
  + apply (ev_SS 0 ev_0).
  + apply ev_sum. apply IHE1. apply IHE2.
 - intros E. induction E.
  + apply ev'_0.
  + assert (H: ev' (2 + n)). 
    { apply ev'_sum. apply ev'_2.  apply IHE. }
    unfold plus in H. apply H.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m E1 E2. induction E2 as [|n' E2' IH].
  - simpl in E1. apply E1.
  - rewrite plus_comm in E1. rewrite <- plus_n_Sm in E1. rewrite <- plus_n_Sm in E1. inversion E1. apply IH.  rewrite plus_comm. apply H0.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p E1 E2. apply ev_ev__ev with (n:=(n + n)).
  - rewrite plus_assoc. rewrite plus_comm. SearchAbout plus. rewrite <- plus_assoc. rewrite plus_assoc.
    apply ev_sum with (n:=(p + n)). rewrite plus_comm. apply E2. apply E1.
  - apply ev_even_iff. exists n. SearchAbout plus. Admitted.

Module LeModule.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply (le_S 3 5 (le_S 3 4 (le_S 3 3 (le_n 3)))).
Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H. inversion H. inversion H2.
Qed.

End LeModule.

Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n: nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n: nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation : nat -> nat -> Prop :=
  tr : forall n m, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop :=
  er : forall n m,  0 = 1 -> empty_relation n m.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2. induction H2 as [|o' H3 H4].
  - apply H1.
  - apply le_S. apply H4.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n as [|n' H].
  - apply le_n.
  - apply le_S. apply H.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H. induction H as [|m' H' IH].
  - apply le_n.
  - apply le_S. apply IH.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  - apply le_n.
  - apply le_trans with (n:= S n). apply le_S. apply le_n. apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b. induction b as [|b' IH].
  - rewrite plus_comm. simpl. apply le_n.
  - SearchAbout plus. rewrite <- plus_n_Sm. apply le_S. apply IH.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
  intros n1 n2 m H. split.
  - apply le_trans with (n:= S (n1 + n2)).
    + apply n_le_m__Sn_le_Sm. apply le_plus_l.
    + apply H.
  - apply le_trans with (n:= S (n1 + n2)).
    + apply n_le_m__Sn_le_Sm. rewrite plus_comm. apply le_plus_l.
    + apply H.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros n m H. apply le_S. apply H.
Qed.

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  intros n m H.
  generalize dependent m.  
  induction n as [|n' IH].
  - intros m. intros H. apply O_le_n.
  - intros m. intros H. destruct m as [|m'].
    + inversion H.
    + simpl in H. apply n_le_m__Sn_le_Sm. apply IH. apply H.
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m' IH].
  - intros n H. inversion H. reflexivity.
  - intros n H. destruct n as [|n'].
    + reflexivity.
    + simpl. apply IH. apply Sn_le_Sm__n_le_m. apply H.
Qed.

Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  intros n m o H1 H2. apply leb_correct. apply leb_complete in H1. apply leb_complete in H2.
  apply le_trans with (n:=m). apply H1. apply H2.
Qed.

Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  split. apply leb_complete. apply leb_correct.
Qed.


Module R.
