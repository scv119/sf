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
        

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n : nat => if oddb n then Podd n else Peven n.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false ->  Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even. destruct (oddb n) eqn : H3.
  - apply H1. reflexivity.
  - apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd:
  forall (Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n ->
  oddb n = true ->
  Podd n.
Proof.
  intros Podd Peven n H1 H2. unfold combine_odd_even in H1. rewrite H2 in H1. apply H1.
Qed.

Theorem combine_odd_even_elim_even:
  forall (Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n ->
  oddb n = false ->
  Peven n.
Proof.
  intros Podd Peven n H1 H2. unfold combine_odd_even in H1. rewrite H2 in H1. apply H1.
Qed.

Check plus_comm.

Lemma plus_comm3_take2 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite (plus_comm p).
  reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP. Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.


Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.


Lemma plus_comm_ext : plus = fun n m => m + n.
Proof.
  apply functional_extensionality. intros n.
  apply functional_extensionality. intros m.
  apply plus_comm.
Qed.

Print Assumptions plus_comm_ext.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.


Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].


Lemma tr_rev_aux_correct :
  forall T (l1 l2 : list T),
    rev_append l1 l2 = rev l1 ++ l2.
Proof.
  intros T l1.
  induction l1 as [|t l3 IHl].
  - reflexivity.
  - simpl. SearchAbout ((_ ++ _) ++ _). symmetry. rewrite <- app_assoc. rewrite IHl. reflexivity.
Qed.

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X. apply functional_extensionality.
  intros x. unfold tr_rev. rewrite tr_rev_aux_correct.
 SearchAbout (_ ++ []).
  apply app_nil_r.
Qed.

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  intros n. induction n as [|m].
  - exists 0. reflexivity.
  - destruct IHm. destruct (evenb m) eqn: H1.
    + exists x. rewrite evenb_S. rewrite H1. simpl. rewrite H. reflexivity.
    + exists (S x). rewrite evenb_S. rewrite H1. simpl. rewrite H. reflexivity.
Qed.

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.


Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - unfold andb. destruct b1.
    + intros H. split. reflexivity. apply H.
    + intros H. inversion H.
  - intros [H1 H2]. rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - destruct b1.
    + intros H. left. reflexivity.
    + simpl. intros H. right. apply H.
  - intros [H | H].
    + rewrite H. reflexivity.
    + rewrite H. destruct b1. reflexivity. reflexivity.
Qed.


Theorem beq_nat_false_iff : forall x y : nat,
  beq_nat x y = false <->  x <> y.
Proof.
 intros x y. split.
generalize dependent y.
  - induction x as [|x'].
    + simpl. destruct y. intros H. inversion H. intros H. unfold not. intros H1. inversion H1.
    + intros y H. destruct y.
      * unfold not. intros H1. inversion H1.
      * simpl in H. apply IHx' in H. unfold not. intros H1. inversion H1.  rewrite H2 in H. unfold not in H. apply H. reflexivity.
  -  unfold not. generalize dependent y. induction x as [|x'].
    + simpl. destruct y.
      * intros H. exfalso. apply H. reflexivity.
      * intros H.  reflexivity.
    + intros y H. destruct y.
      * simpl. reflexivity.
      * simpl. apply IHx'. intros H1. apply H. apply f_equal. apply H1.
Qed.


Fixpoint beq_list {A} (beq : A -> A -> bool)
                  (l1 l2 : list A) : bool  :=
  match l1, l2 with 
  | [], [] => true
  | s::t, u::v => if beq s u then beq_list beq t v else false
  | _, _ => false
  end.

Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
  intros A beq H. split.
  generalize dependent l2.
  - induction l1 as [|x l1' IHl1'].
    + intros l2. intros H1. destruct l2. reflexivity. simpl in H1. inversion H1.
    + intros l2. induction l2 as [|y l2' IHl2'].
      * intros H1. simpl in H1. inversion H1.
      * intros H1. simpl in H1. destruct (beq x y) eqn:Heq.
        apply H in Heq. apply IHl1' in H1. rewrite H1. rewrite Heq. reflexivity.
        inversion H1.
  - generalize dependent l2. induction l1 as [|x l1' IHl'].
    + intros l2 H1. rewrite <- H1. reflexivity.
    + intros l2. induction l2 as [|y l2' IHl2'].
      * intros H1. simpl in H1. inversion H1.
      * intro H1. inversion H1. simpl. destruct (beq y y) eqn:Heq.
         rewrite <- H3. apply IHl'. reflexivity.
         destruct H1. assert (H4 : y = y). { reflexivity. } apply H in H4. rewrite H4 in Heq. inversion Heq.
Qed.


Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l. split.
  - induction l as [|x l' IHl'].
    + simpl. intros H. apply I.
    + simpl. intros H. apply andb_true_iff in H. destruct H. split.
      * apply H.
      * apply IHl'. apply H0.
  - induction l as [|x l' IHl'].
    + simpl. intros H. reflexivity.
    + simpl. intros [H1 H2]. rewrite H1. apply IHl' in H2. rewrite H2. reflexivity.
Qed.

(* forallb test l = false <-> exists x, x in l -> test x = false *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.


Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P. unfold not. intros H. apply H.
  right.
  intros H1. apply H. left. apply H1.
Qed.

Theorem test : forall (P : Prop),
  ~~ P -> P.
Proof.
  intros P. unfold not. intros H.
Abort.

Theorem not_exists_dist:
  excluded_middle ->
  forall (X : Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof. 
  intros H X P H1 x. unfold excluded_middle in H. assert (P x \/ ~ P x). { apply H. } 
  destruct H0 as [H2 | H2].
  - apply H2.
  - exfalso. unfold not in H1. apply H1. exists x. apply H2.
Qed.

Definition peirce := forall P Q: Prop,
  ((P-> Q)-> P) -> P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).

Theorem peirce_execluded_middle:
  excluded_middle -> peirce.
Proof.
  unfold excluded_middle. unfold peirce.
  intros H. intros P Q. intros H1. assert (P  \/ ~ P ). { apply H. }
  destruct H0 as [H2 | H2].
  - apply H2.
  - apply H1. intros H3. exfalso. apply H2. apply H3.
Qed. 

Lemma peirce_lemma1:
  forall P Q, ~(P \/ Q) -> ~P.
Proof.
  intros P Q H1.
  unfold not. intros H2. unfold not in H1. apply H1. left. apply H2.
Qed.

Theorem execluded_middle_peirce:
 peirce ->  excluded_middle.
Proof.
  unfold excluded_middle. unfold peirce.
  intros H. intros P. assert (H1: (((P \/ ~P) -> False) -> (P \/ ~P)) -> (P \/ ~P) ). apply H.
  apply H1. intros H2. right.  apply peirce_lemma1 in H2. apply H2.
Qed.

Theorem execluded_middle_to_double_negation_elimination:
  excluded_middle -> double_negation_elimination.
Proof.
  unfold excluded_middle. unfold double_negation_elimination.
  intros H P. unfold not. assert (P  \/ ~ P ). { apply H. }
  destruct H0 as [H1 | H1].
  - intros H2. apply H1.
  - intros H2. exfalso. apply H2. apply H1.
Qed.

Theorem double_negation_elimination_to_execluded_middle:
  double_negation_elimination -> excluded_middle.
Proof.
  unfold excluded_middle. unfold double_negation_elimination.
  intros H P. apply H. apply excluded_middle_irrefutable.
Qed.

Theorem execluded_middle_to_de_morgan_not_and_not:
  excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle. unfold de_morgan_not_and_not.
  intros H P Q H1. assert (P  \/ ~ P ). { apply H. }
  destruct H0 as [H2 | H2].
  - left. apply H2.
  - assert (Q  \/ ~ Q ). { apply H. }  destruct H0 as [H3 | H3].
    + right. apply H3.
    + exfalso. apply H1. split. apply H2. apply H3.
Qed.

Theorem de_morgan_not_and_not_to_execluded_middle:
  de_morgan_not_and_not -> excluded_middle.
Proof.
  unfold excluded_middle. unfold de_morgan_not_and_not.
  intros H P. assert ( ~ (~ P /\ ~ (~P)) -> P \/ (~P) ). { apply H. }
  apply H0. unfold not. intros [H1 H2]. apply H2. apply H1.
Qed.

Theorem execluded_middle_to_implies_to_or:
  excluded_middle -> implies_to_or.
Proof.
  unfold excluded_middle. unfold implies_to_or.
  intros H P Q H1. assert (P  \/ ~ P ). { apply H. }
   destruct H0 as [H2 | H2].
  - right. apply H1. apply H2.
  - left. apply H2.
Qed.


Theorem implies_to_or_to_execluded_middle:
  implies_to_or -> excluded_middle.
Proof.
  unfold excluded_middle. unfold implies_to_or.
  intros H P. assert ((P -> P) -> ~ P \/ P ). { apply H. }
  apply or_commut. apply H0. intros H1. apply H1.
Qed.