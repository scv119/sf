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
