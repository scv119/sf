Add LoadPath "/Users/chenshen/src/sf/".

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.

Module AExp.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(*
BNF: 
    a ::= nat
        | a + a
        | a - a
        | a * a

    b ::= true
        | false
        | a = a
        | a ≤ a
        | not b
        | b and b

*)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum a => a
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Fixpoint beval (a : bexp) : bool :=
  match a with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2 => leb (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound : forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - reflexivity.
  - destruct a1.
    + destruct n.
      * simpl. apply IHa2.
      * simpl. rewrite IHa2. reflexivity.
    + simpl. rewrite IHa2. simpl in IHa1. rewrite IHa1. reflexivity.
    + simpl. rewrite IHa2. simpl in IHa1. rewrite IHa1. reflexivity.
    + simpl. rewrite IHa2. simpl in IHa1. rewrite IHa1. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. (* this just does reflexivity *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* just reflexivity would have failed *)
  apply HP. (* we can still finish the proof in some other way *)
Qed.

Lemma foo' : forall n, leb 0 n = true.
Proof.
  intros.
  (* destruct the current goal *)
  destruct n; 
  (* then simpl each resulting subgoal *)
  simpl; 
  (* and do reflexivity on each resulting subgoal *)
  reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... but the remaining cases -- ANum and APlus -- 
       are different: *)
    try reflexivity.
  - (* APlus *)
    destruct a1;
      (* Again, most cases follow directly by the IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* The interesting case, on which the try...
       does nothing, is when e1 = ANum n. In this
       case, we have to destruct n (to see whether
       the optimization applies) and rewrite with the
       induction hypothesis. *)
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue => b
  | BFalse => b
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot _ => b
  | BAnd _ _ => b
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros b;
  induction b;
    try (simpl; reflexivity);
    simpl; repeat (rewrite optimize_0plus_sound'); reflexivity.
Qed.


Fixpoint optimize_0 (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0 e2
  | APlus e1 e2 => APlus (optimize_0 e1) (optimize_0 e2)
  | AMinus e1 (ANum 0) => optimize_0 e1
  | AMinus e1 e2 => AMinus (optimize_0 e1) (optimize_0 e2)
  | AMult (ANum 0) _ => ANum 0
  | AMult e1 e2 => AMult (optimize_0 e1) (optimize_0 e2)
  end.

Lemma sound_lemma : forall a,
  a - 0 = a.
Proof.
  destruct a; simpl; reflexivity.
Qed.

Theorem optimize_0_sound : forall a,
  aeval (optimize_0 a) = aeval a.
Proof.
  intros a.
  induction a;
    try (simpl; reflexivity).
  - destruct a1;
    try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    + destruct n ; simpl; rewrite IHa2; reflexivity.
  - destruct a2;
    try (simpl; simpl in IHa2; rewrite IHa2; rewrite IHa1; reflexivity).
    + destruct n; simpl; rewrite IHa1; try rewrite sound_lemma; reflexivity.
  - destruct a1;
      try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    + destruct n; simpl; try rewrite IHa2; reflexivity.
Qed.

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

Require Import Coq.omega.Omega.

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n : nat), aevalR (ANum n) n
  | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
      aevalR e1 n1 -> aevalR e2 n2 -> aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
      aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
      aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMult e1 e2) (n1 * n2).

Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.


Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  split.
  - intros H.
    induction H; subst; reflexivity.
  - generalize dependent n.
    induction a; simpl; intros; subst; constructor; try  apply IHa1; try apply IHa2; reflexivity.
Qed.

Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : bevalR BTrue true
  | E_BFalse : bevalR BFalse false
  | E_BEq : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> bevalR (BEq a1 a2) (beq_nat n1 n2)
  | E_BLe : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> bevalR (BLe a1 a2) (leb n1 n2)
  | E_BNot : forall (e : bexp) (b : bool),
      bevalR e b -> bevalR (BNot e) (negb b)
  | E_BAnd : forall (e1 e2 : bexp) (b1 b2 : bool),
      (bevalR e1 b1) -> (bevalR e2 b2) -> bevalR (BAnd e1 e2) (andb b1 b2).

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  split.
  - intros H.
    induction H; simpl; try apply aeval_iff_aevalR in H; try apply aeval_iff_aevalR in H0; subst; try reflexivity.
  - generalize dependent bv.
    induction b; simpl; intros; subst; constructor; 
    try apply aeval_iff_aevalR; 
    try apply IHb; 
    try apply IHb1; try apply IHb2; 
    reflexivity.
Qed.

End AExp.


