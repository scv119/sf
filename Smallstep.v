Add LoadPath "/Users/chenshen/src/sf/".
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.
Require Import Imp.

Inductive tm : Type :=
  | C : nat -> tm (* Constant *)
  | P : tm -> tm -> tm. (* Plus *)

(* BigStep *)
Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P a1 a2 => evalF a1 + evalF a2
  end.

Reserved Notation " t '\\' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
    C n \\ n
  | E_Plus : forall t1 t2 n1 n2,
    t1 \\ n1 ->
    t2 \\ n2 ->
    P t1 t2 \\ (n1 + n2)
  where " t '\\' n " := (eval t n).

Module SimpleArith1.

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
    P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
    t1 => t1' ->
    P t1 t2 => P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
    t2 => t2' ->
    P (C n1) t2 => P (C n1) t2'

where " t '=>' t' " := (step t t').

Example test_step_1 :
  P (P (C 0) (C 3))
    (P (C 2) (C 4))
  =>
  P (C (0 + 3))
    (P (C 2) (C 4)).
Proof. apply ST_Plus1. apply ST_PlusConstConst. Qed.

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
      =>
      P
        (C 0)
        (P
          (C 2)
          (C (0 + 3))).
Proof. apply ST_Plus2. apply ST_Plus2.  apply ST_PlusConstConst. Qed.

End SimpleArith1.

Definition relation (X:Type) := X -> X -> Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2. 
  - inversion Hy2.
    + reflexivity.
    + inversion H2.
    + inversion H2.
  - inversion Hy2.
    + rewrite <- H0 in Hy1. inversion Hy1.
    +  rewrite <- (IHHy1 t1'0).
        reflexivity. assumption.
    + rewrite <- H in Hy1. inversion Hy1.
  - inversion Hy2.
    + rewrite <- H1 in Hy1. inversion Hy1.
    + inversion H2.
    + rewrite <- (IHHy1 t2'0). reflexivity. assumption.

Qed.

End SimpleArith2.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Module SimpleArith3.
Import SimpleArith1.

Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try solve_by_invert.
  - (* ST_PlusConstConst *) reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_Plus2 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith3.

Inductive value : tm -> Prop :=
  v_const : forall n, value (C n).

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          P (C n1) (C n2)
      => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 => t1' ->
        P t1 t2 => P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 -> (* <----- n.b. *)
        t2 => t2' ->
        P v1 t2 => P v1 t2'

  where " t '=>' t' " := (step t t').

Theorem step_deterministic : 
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; subst;  try solve_by_invert; intros y2 Hy2.
  - inversion Hy2.
    + reflexivity.
    + inversion H2.
    + inversion H3.
  - inversion Hy2.
    + rewrite <- H0 in Hy1. inversion Hy1.
    + apply IHHy1 in H2. rewrite H2. reflexivity.
    + subst. inversion H1. rewrite <- H in Hy1. inversion Hy1.
  - inversion Hy2.
    + rewrite <- H2 in Hy1. inversion Hy1.
    + inversion H. subst. inversion H3.
    + apply IHHy1 in H4. rewrite H4. reflexivity.
Qed.

Theorem strong_progress : forall t,
  value t \/ (exists t', t => t').
Proof.
  intros t. induction t.
  - left. constructor.
  - inversion IHt1.
   + destruct IHt2.
    * right. destruct H0. destruct H. exists (C (n0 + n)). constructor.
    * right. destruct H0. exists (P t1 x). apply  ST_Plus2; assumption.
   +  destruct H. right. exists (P x t2). apply ST_Plus1. assumption.
Qed.