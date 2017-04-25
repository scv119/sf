Add LoadPath "/Users/chenshen/src/sf/".

Require Import Coq.Arith.Arith.
Require Import Maps.
Require Import Imp.
Require Import Smallstep.

Hint Constructors multi.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Definition value (t: tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold update.

Reserved Notation "t1 '=>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) => t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) => t2
  | ST_If : forall t1 t1' t2 t3,
      t1 => t1' ->
      (tif t1 t2 t3) => (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 => t1' ->
      (tsucc t1) => (tsucc t1')
  | ST_PredZero :
      (tpred tzero) => tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) => t1
  | ST_Pred : forall t1 t1',
      t1 => t1' ->
      (tpred t1) => (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) => ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) => tfalse
  | ST_Iszero : forall t1 t1',
      t1 => t1' ->
      (tiszero t1) => (tiszero t1')

where "t1 '=>' t2" := (step t1 t2).

Hint Constructors step.

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (tsucc ttrue). unfold stuck. unfold step_normal_form. split.
  - unfold not. intros H. inversion H. inversion H0. subst. inversion H2.
  - unfold not. intros. inversion H. inversion H0. inversion H0. inversion H2.
Qed.

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros. inversion H.
  - unfold step_normal_form. intros contra. inversion H0; subst; inversion contra; inversion H1.
  - unfold step_normal_form. induction H0. 
    + intros contra. inversion contra. inversion H0.
    + intros contra. inversion contra. inversion H1. subst. assert (value t) by auto. apply IHnvalue in H2 .
      eauto.
Qed.
    
Ltac inv H := inversion H; subst; clear H.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic. intros x. induction x; intros; inversion H; subst; clear H.
  - inversion H0; subst. reflexivity. inversion H4.
  - inversion H0; subst. reflexivity. inversion H4.
  - inversion H0; subst. inversion H5. inversion H5. assert (t1' = t1'0) by auto. subst. auto.
  - inversion H0; subst. assert (t1' = t1'0) by auto. subst. auto.
  - inversion H0; subst. reflexivity. inversion H0. inversion H1.
  - inversion H0; subst. reflexivity. assert (value (tsucc y1)) by auto. apply value_is_nf in H.
    unfold step_normal_form in H. exfalso. apply H. eauto.
  - inversion H0; subst. inversion H2. 
    assert (value (tsucc y2)) by auto. apply value_is_nf in H.
    unfold step_normal_form in H. exfalso. apply H. eauto. apply f_equal. auto.
  - inversion H0; subst. reflexivity. inversion H1.
  - inversion H0; subst. reflexivity. assert (value (tsucc t1)) by auto. apply value_is_nf in H.
    unfold step_normal_form in H. exfalso. apply H. eauto.
  - inversion H0; subst.
    + inversion H2.
    + assert (value (tsucc t1)) by auto. apply value_is_nf in H.
    unfold step_normal_form in H. exfalso. apply H. eauto.
    + apply f_equal. auto.
Qed.
    
  

