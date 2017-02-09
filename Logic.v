Add LoadPath "/Users/chenshen/src/sf/".
Require Export Tactics.

Check forall n : nat, n = 2.


Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.


Definition is_three (n :nat) : Prop :=
  n = 3.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Check injective.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

Check @eq.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro: forall A B :Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_example'  : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H. destruct n eqn:Heq1.
  - destruct m eqn:Heq2.
    + split.
      * reflexivity.
      * reflexivity.
    + inversion H.
  - inversion H.
Qed.

Lemma proj2 : forall P Q: Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [H1 H2]. apply H2. Qed.

Theorem and_commut : forall P Q: Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [H1 H2]. 
  split.
  - apply H2.
  - apply H1.
Qed.

Check and.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]]. 
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left. apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  -right. reflexivity.
Qed.

Lemma mult_eq_0:
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  destruct n.
  - left. reflexivity.
  - inversion H. apply and_exercise in H1. destruct H1.
    right. rewrite H1. rewrite H0. reflexivity.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

Module MyNot.

Definition not (P: Prop) := P -> False.

Check not.

Notation "~ x" := (not x) : type_scope.

End MyNot.

Theorem ex_falso_quodlibet : forall (P : Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra. Qed.

Fact not_implies_our_not : forall (P : Prop),
  ~ P -> (forall (Q : Prop), P -> Q).
Proof.
  intros P H Q HP. apply H in HP. destruct HP. Qed.

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra.
Qed.

Theorem not_False:
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q: Prop,
  (P /\ ~ P) -> Q.
Proof.
  intros P Q [H1 H2]. unfold not in H2. apply H2 in H1. destruct H1. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not. intros H1. apply H1. apply H.
Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H. unfold not. intros HQ. intros HP.
  apply HQ. apply H. apply HP.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. intros P. unfold not. intros [H H1]. apply H1. apply H. Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

