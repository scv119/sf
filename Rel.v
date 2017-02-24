Add LoadPath "/Users/chenshen/src/sf/".

Require Export IndProp.

Definition relation (X: Type) := X -> X -> Prop.

Print le.

Check le : nat -> nat -> Prop.

Check le : relation nat.

(* Partial Functions *)

Definition partial_function {X : Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.
  
Print next_nat.

Theorem next_nat_partial_function : 
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2. inversion H1. inversion H2. reflexivity.
Qed.

Theorem le_not_a_partial_function :
  ~(partial_function le).
Proof.
  unfold not. unfold partial_function.
  intros H. assert (0 = 1) as Nonsense. {
    apply H with (x:=0).
    - apply le_n.
    - apply le_S. apply le_n.
  }
  inversion Nonsense.
Qed.

Theorem total_relation_not_partial_function :
  ~(partial_function total_relation).
Proof.
  unfold not. unfold partial_function.
  intros Hc. assert (0 = 1) as Nonsense. {
    apply Hc with (x:= 0); apply tr.
  }
  inversion Nonsense.
Qed.

Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2. inversion H1. inversion H.
Qed.

SearchAbout empty_relation.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n. Qed.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  unfold transitive.
  intros  n m o Hn Hm.
  induction Hm.
  - apply Hn.
  - apply le_S. apply IHHm.
Qed.

Theorem lt_trans :
  transitive lt.
Proof.
  unfold transitive. unfold lt.
  intros  n m o Hn Hm.
  induction Hm.
  - apply le_S. apply Hn.
  - apply le_S. apply IHHm.
Qed.

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold transitive. unfold lt.
   intros  n m o Hn Hm. induction o as [|o' IHo].
  - inversion Hm.
  - apply le_S. apply IHo. 
Abort.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (b:= (S n)).
  - apply le_S. apply le_n.
  - apply H.
Qed.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros n m H. inversion H.
  - apply le_n.
  - apply le_Sn_le. apply H1.
Qed.

(* 
  Theorem: For every n, ¬ (S n ≤ n)
  Induction on n.
    * n is 0, we need to prove1 <= 0 implies False, which is nonsense.
    * suppose n is S m' and we have S m' <= m' implies False. We need
      to prove S (S m') <= (S m') implies False too.
    * Using le_S_n, we know   S (S m') <= (S m') implies S m' <= m', which 
      implies False.
  Qed
*)

Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  intros n. induction n as [|n' IHn].
  - intros H. inversion H.
  - intros H. apply le_S_n in H. apply IHn. apply H.
Qed.

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric:
  ~(symmetric le).
Proof.
  unfold symmetric. intros H. assert (1 <= 0) as nonsense. { apply H. repeat constructor. } inversion nonsense.
Qed.

Definition antisymmetric {X: Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Theorem le_antisymmetric:
  antisymmetric le.
Proof.
  unfold antisymmetric. intros a. induction a.
  - intros b H1 H2. inversion H2. reflexivity.
  - intros b H1 H2. destruct b.
    + inversion H1.
    + apply f_equal. apply le_S_n in H1. apply le_S_n in H2. apply IHa; assumption.
Qed.

Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  intros n m p H1 H2. destruct m.
  - inversion H1.
  - unfold lt in H1. apply le_S_n in H1. apply le_S_n in H2. apply le_trans with (b:=m); assumption.
Qed.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).
