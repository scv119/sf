Add LoadPath "/Users/chenshen/src/sf/".

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Imp.
Require Import Maps.

Definition Assertion := state -> Prop.

Module ExAssertions.
Definition as1 : Assertion := fun st => st X = 3.
(* state has st X equals 3 *)
Definition as2 : Assertion := fun st => st X <= st Y.
(* state has st X less or equal than st Y  *)
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
(* state has st X less or equal than st Y , or st X = 3 *)
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
(* any state *)
Definition as6 : Assertion := fun st => False.
(* none of the state *)
End ExAssertions.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.

Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* 
Hoare Triple:
"If command c is started in a state satisfying assertion P, and if c eventually terminates 
in some final state, then this final state will satisfy the assertion Q."
*)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
    c / st \\ st' ->
    P st ->
    Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_post_true : forall(P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros. unfold hoare_triple. intros. apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros. unfold hoare_triple. intros. exfalso. apply H in H1. assumption.
Qed.

(* Assignment rule:

{{ Q [X |-> a] }} X ::= a {{ Q }}

 To conclude that an arbitrary property Q holds after X ::= a, we need to assume that Q 
 holds before X ::= a, but with all occurrences of X replaced by a in Q. 

  where "Q [X |-> a]" is pronounced "Q where a is substituted for X".
*)

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (t_update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  intros. unfold hoare_triple. intros.
  inversion H. subst. unfold assn_sub in H0. assumption.
Qed.

Example assn_sub_example :
  {{(fun st => st X = 3) [X |-> ANum 3]}}
  (X ::= (ANum 3))
  {{fun st => st X = 3}}.
Proof.
  apply hoare_asgn. Qed.

Example assn_sub_ex1 :
  {{( fun st => st X <= 5 ) [X |-> APlus (AId X) (ANum 1)] }}
  (X ::= APlus (AId X) (ANum 1))
  {{ fun st => st X <= 5}}.
Proof.
  apply hoare_asgn. Qed.

Example assn_sub_ex2:
  {{(fun st => (0 <= (st X)) /\ (st X <= 5)) [ X |-> ANum 3]}}
  ( X::= ANum 3)
  {{ fun st => (0 <= (st X)) /\ (st X <= 5) }}.
Proof.
  apply hoare_asgn. Qed.