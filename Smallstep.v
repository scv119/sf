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

Definition normal_form {X: Type} (R: relation X) (t: X) : Prop  :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  intros. unfold normal_form. unfold not. intros. destruct H0. destruct H. inversion H0.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof.
  unfold normal_form. intros. 
  assert (G : value t \/ exists t', t => t').
  { (* Proof of assertion *) apply strong_progress. }
  inversion G.
  - assumption.
  - exfalso. apply H. assumption.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf. Qed.

Module Temp1.

Inductive value : tm -> Prop :=
| v_const : forall n, value (C n)
| v_funny : forall t1 n2, (* <---- *)
              value (P t1 (C n2)).

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 => t1' ->
      P t1 t2 => P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 => t2' ->
      P v1 t2 => P v1 t2'

  where " t '=>' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  exists (P (C 1) (C 2)). split.
  - apply v_funny.
  - unfold not, normal_form. intros. apply H. exists (C (1 + 2)). constructor.
Qed. 

End Temp1.

Module Temp2.

Inductive value : tm -> Prop :=
| v_const : forall n, value (C n).

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n, (* <---- *)
      C n => P (C n) (C 0)
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 => t1' ->
      P t1 t2 => P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 => t2' ->
      P v1 t2 => P v1 t2'

  where " t '=>' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  exists (C 1). split.
  - constructor.
  - unfold not, normal_form. intros. apply H. exists (P (C 1) (C 0)). constructor.
Qed.

End Temp2.

Module Temp3.

Inductive value : tm ->  Prop :=
  | v_const : forall n, value (C n).

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm ->  tm ->  Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 => t1' -> 
      P t1 t2 => P t1' t2

  where " t '=>' t' " := (step t t').


Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  exists  (P (C 1) (P (C 1) (C 1))). split.
  -  unfold not. intros. inversion H.
  - unfold normal_form, not. intros. destruct H. inversion H. inversion H3.
Qed.

End Temp3.