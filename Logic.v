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

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation " P <-> Q " := (iff P Q)
                        (at level 95, no associativity)
                        : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H. unfold iff in H. destruct H as [HA HB]. unfold iff.
  split.
  - apply HB.
  - apply HA.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  - intros H. rewrite H. unfold not. intros H'. inversion H'.
Qed.


Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P. split.
  - intros H. apply H.
  - intros H. apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R [H1 H2] [H3 H4]. split.
  - intros H5. apply H3. apply H1. apply H5.
  - intros H5. apply H2. apply H4. apply H5.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R ) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - intros [H1 | [H3 H4]].
   + split.
    * left. apply H1.
    * left. apply H1.
   + split.
    * right. apply H3.
    * right. apply H4.
  - intros [[H1|H2] [H3|H4]].
    * left. apply H1.
    * left. apply H1.
    * left. apply H3.
    * right. split. apply H2. apply H4.
Qed.

Require Import Coq.Setoids.Setoid.


Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     n = 0 ∨ m = 0 *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example :
 forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.


Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm. Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H. unfold not. intros H1. inversion H1 as [x Hx]. apply Hx in H. apply H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros [x [H1 | H2]].
    + left. exists x. apply H1.
    + right. exists x. apply H2.
  - intros [[x H] | [x H]].
    + exists x. left. apply H.
    + exists x. right. apply H.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [3; 4; 5].
Proof.
  simpl. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l. split.
  - induction l as [|x' l' IHl'].
    + simpl. intros [].
    + simpl. intros [H | H].
      * exists x'. split. apply H. left. reflexivity.
      * apply IHl' in H. destruct H as [x'' [H1 H2]]. exists x''. split.
        apply H1. right. apply H2.
  - intros [x [H1 H2]]. induction l as [|y' l' IHl'].
    + simpl. inversion H2.
    + simpl. simpl in H2. destruct H2 as [H3 | H4].
      * left. rewrite  H3. apply H1.
      * right. apply IHl'. apply H4.
Qed.

Lemma in_app_iff : forall A l l' (a : A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a.
  induction l as [| x m IHm].
  - simpl. split.
    + intros H. right. apply H.
    + intros [[] | H1]. apply H1.
  - simpl. split.
    + intros [ H | H].
      *  apply or_assoc. left. apply H.
      *   apply or_assoc. right. destruct IHm. apply H0. apply H.
    +  intros H. apply or_assoc in H. destruct H as [H1 | H2].
      * left. apply H1.
      *  right. destruct IHm as [H1 H3]. apply H3. apply H2.
Qed.

Fixpoint All {T} (P : T -> Prop) (l : list T) : Prop  :=
  match l with
  | [] => True
  | t :: l' => P t /\ (All P l')
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l.
  - induction l as [|x' l' IHl'].
    + simpl. split. intros H. apply I. intros H. intros x. intros [].
    + simpl. destruct IHl' as [H1 H2]. split.
      * intros H3. split. 
          apply H3. left. reflexivity.
          apply H1. intros x1. intros H4. apply H3. right. apply H4.
      * intros [H3 H4]. intros x. intros [H | H].
          rewrite <- H. apply H3.
          apply H2. apply H4. apply H.
Qed.
        
