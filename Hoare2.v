Add LoadPath "/Users/chenshen/src/sf/".

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Maps.
Require Import Imp.
Require Import Hoare.

(*
Exercise: 2 stars (if_minus_plus_reloaded)
Fill in valid decorations for the following program:
   {{ True }}
  IFB X <= Y THEN
      {{ True /\ X <= Y }} ->>
      {{ Y = X + (Y - X) }}
    Z ::= Y - X
      {{ Y = X + Z }}
  ELSE
      {{ True /\ ~(X <= Y) }} ->>
      {{ X + Z = X + Z }}
    Y ::= X + Z
      {{ Y = X + Z }}
  FI
    {{ Y = X + Z }}
*)

(* Example: Reduce to Zero

        (1)      {{ True }}
               WHILE X <> 0 DO
        (2)        {{ True /\ X <> 0 }} ->>
        (3)        {{ True }}
                 X ::= X - 1
        (4)        {{ True }}
               END
        (5)      {{ True /\ X = 0 }} ->>
        (6)      {{ X = 0 }}

*)

Definition reduce_to_zero' : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem reduce_to_zero_correct' :
  {{fun st => True}}
  reduce_to_zero'
  {{fun st => st X = 0}}.
Proof.
  unfold reduce_to_zero'.
  (* First we need to transform the postcondition so
     that hoare_while will apply. *)
  eapply hoare_consequence_post.
  apply hoare_while.
  - (* Loop body preserves invariant *)
    (* Need to massage precondition before hoare_asgn applies *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    (* Proving trivial implication (2) ->> (3) *)
    intros st [HT Hbp]. unfold assn_sub. apply I.
  - (* Invariant and negated guard imply postcondition *)
    intros st [Inv GuardFalse].
    unfold bassn in GuardFalse. simpl in GuardFalse.
    (* SearchAbout helps to find the right lemmas *)
    SearchAbout [not true].
    rewrite not_true_iff_false in GuardFalse.
    SearchAbout [negb false].
    rewrite negb_false_iff in GuardFalse.
    SearchAbout [beq_nat true].
    apply beq_nat_true in GuardFalse.
    apply GuardFalse. Qed.

(* Example: Division

      (1)    {{ True }} ->>
      (2)    {{ n * 0 + m = m }}
           X ::= m;;
      (3)    {{ n * 0 + X = m }}
           Y ::= 0;;
      (4)    {{ n * Y + X = m }}
           WHILE n <= X DO
      (5)      {{ n * Y + X = m /\ n <= X }} ->>
      (6)      {{ n * (Y + 1) + (X - n) = m }}
             X ::= X - n;;
      (7)      {{ n * (Y + 1) + X = m }}
             Y ::= Y + 1
      (8)      {{ n * Y + X = m }}
           END
      (9)    {{ n * Y + X = m /\ X < n }}

*)

(* 

Exercise: 2 stars (slow_assignment)
A roundabout way of assigning a number currently stored in X to the variable Y is to start Y at 0, 
then decrement X until it hits 0, incrementing Y at each step. 
Here is a program that implements this idea:
        {{ X = m }}
      Y ::= 0;;
      WHILE X ≠ 0 DO
        X ::= X - 1;;
        Y ::= Y + 1
      END
        {{ Y = m }}

Answer:

      {{ X = m }}
      Y ::= 0;;
      {{ Y + X = m }}
      WHILE X ≠ 0 DO
      {{ Y + X = m /\ X <> 0 }} ->>
      {{ (Y + 1) + (X - 1) = m }}
        X ::= X - 1;;
      {{ (Y + 1) + X = m }}
        Y ::= Y + 1
      {{ Y + X = m }}
      END
      {{ Y + X = m /\ X = 0}} ->>
      {{ Y = m }}

*)

(*
Exercise: 3 stars, optional (add_slowly_decoration)
The following program adds the variable X into the variable Z 
by repeatedly decrementing X and incrementing Z.
      
      WHILE X ≠ 0 DO
         Z ::= Z + 1;;
         X ::= X - 1
      END

Answer: 

{{ X = m /\ Z = n }} ->>
{{ X + Z = m + n }}
WHILE X ≠ 0 DO
{{ X + Z = m + n /\ X <> 0 }} ->>
{{ (X - 1) + (Z + 1) = m + n }}
  Z ::= Z + 1;;
{{ (X - 1) + Z = m + n }}
  X ::= X - 1
{{ X + Z = m + n }}
END
{{ X + Z = m + n /\ X = 0 }} ->>
{{ Z = m + n }}

*)

(*
        {{ X = m }} ⇾                              (a - OK)
        {{ parity X = parity m }}
      WHILE 2 ≤ X DO
          {{ parity X = parity m ∧ 2 ≤ X }}  ⇾    (c - OK)
          {{ parity (X-2) = parity m }}
        X ::= X - 2
          {{ parity X = parity m }}
      END
        {{ parity X = parity m ∧ X < 2 }}  ⇾       (b - OK)
        {{ X = parity m }}
*)

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof. intros.
  remember (x - 2) as y.
  SearchAbout minus.
  assert (y + 2 = x). { rewrite Heqy. apply Nat.sub_add. apply H. }
  rewrite <- H0. rewrite Nat.add_comm. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity (x) = x.
Proof. intros. destruct x.
  - reflexivity.
  - destruct x.
    + reflexivity.
    + exfalso. apply H. omega.
Qed.

Theorem parity_correct : forall m,
    {{ fun st => st X = m }}
  WHILE BLe (ANum 2) (AId X) DO
    X ::= AMinus (AId X) (ANum 2)
  END
    {{ fun st => st X = parity m }}.
Proof.
  intros m. eapply hoare_consequence_post.
  apply hoare_consequence_pre with (fun st : state => parity (st X) = parity m).
  - apply hoare_while. eapply hoare_consequence_pre. apply hoare_asgn.
    intros st [H0 H1]. unfold assn_sub. simpl. rewrite t_update_eq. rewrite <- H0.
    apply parity_ge_2. unfold bassn in H1. unfold beval in H1. SearchAbout le. apply leb_complete in H1.
    simpl in H1. assumption.
  - intros st H. subst. reflexivity.
  - intros st [H0 H1]. rewrite <- H0. symmetry. apply parity_lt_2.  intros H. apply H1. unfold bassn.
    simpl. remember (st X) as x.
    destruct x. inversion H. destruct x. inversion H. inversion H3. reflexivity.
Qed.

(*       {{ X=m }}
    Z ::= 0;;
    WHILE (Z+1)*(Z+1) ≤ X DO
      Z ::= Z+1
    END
      {{ Z*Z≤m ∧ m<(Z+1)*(Z+1) }}
*)

(* 
    {{ X = m }}
  Y ::= 0;;
  Z ::= 0;;
  WHILE  Y ≠ X  DO
    Z ::= Z + X;;
    Y ::= Y + 1
  END
    {{ Z = m*m }}
*)
