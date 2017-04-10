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

Module Temp4.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_true : value ttrue
  | v_false : value tfalse.

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tif ttrue t1 t2 => t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 => t2
  | ST_If : forall t1 t1' t2 t3,
      t1 => t1' ->
      tif t1 t2 t3 => tif t1' t2 t3

  where " t '=>' t' " := (step t t').

Theorem strong_progress : forall t,
  value t \/ (exists t', t => t').
Proof.
  intros t. induction t.
  - left. constructor.
  - left. constructor.
  - destruct IHt1.
    + destruct H. 
      * right. exists t2. constructor.
      * right. exists t3. constructor.
    + destruct H. right. exists (tif x t2 t3). constructor. assumption.
Qed.

Theorem step_deterministic :
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 H.
  generalize dependent y2.
 induction H.
  - intros. inversion H. 
    + reflexivity.
    + subst. inversion H4.
  - intros. inversion H.
    + reflexivity.
    + subst. inversion H4.
  - intros. inversion H0.
    + rewrite <- H2 in H. inversion H.
    + rewrite <- H2 in H. inversion H.
    + apply IHstep in H5. rewrite H5. reflexivity.
Qed.

Module Temp5.

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tif ttrue t1 t2 => t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 => t2
  | ST_If : forall t1 t1' t2 t3,
      t1 => t1' ->
      tif t1 t2 t3 => tif t1' t2 t3
  | ST_ShortCircuit : forall t t',
      (t' = ttrue \/ t' = tfalse) ->
      tif t t' t' => t'

  where " t '=>' t' " := (step t t').

Definition bool_step_prop4 :=
         tif
            (tif ttrue ttrue ttrue)
            tfalse
            tfalse
     =>
         tfalse.

Example bool_step_prop4_holds :
  bool_step_prop4.
Proof.
  apply ST_ShortCircuit. right. reflexivity.
Qed.

Theorem not_step_deterministic :
  ~(deterministic step).
Proof.
  unfold not, deterministic. intros. assert (Contra: tfalse = (  tif
            ttrue
            tfalse
            tfalse )).
  { apply H with (          tif
            (tif ttrue ttrue ttrue)
            tfalse
            tfalse ).
    - apply ST_ShortCircuit. right. reflexivity.
    - apply ST_If. constructor.
  }
  inversion Contra.
Qed.

Theorem strong_progress : forall t,
  value t \/ (exists t', t => t').
Proof.
  Admitted.

(* In general, is there any way we could cause strong progress to fail if we took away one or more constructors from the original step relation? Write yes or no and briefly (1 sentence) explain your answer.
 Yes, remove ST_IFTrue then tif ttrue t1 t2 will be stuck. *)

End Temp5.
End Temp4.


Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation " t '=>*' t' " := (multi step t t') (at level 40).

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> (multi R) x y.
Proof.
   intros. apply multi_step with y. assumption. constructor. Qed.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption. Qed.

Lemma test_multistep_1':
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
  =>*
      C ((0 + 3) + (2 + 4)).
Proof.
  eapply multi_step. apply ST_Plus1. apply ST_PlusConstConst.
  eapply multi_step. apply ST_Plus2. apply v_const.
  apply ST_PlusConstConst.
  eapply multi_step. apply ST_PlusConstConst.
  apply multi_refl. Qed.

Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  =>*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  eapply multi_step. apply ST_Plus2. constructor.
  apply ST_Plus2. constructor.  apply ST_PlusConstConst.
  eapply multi_step. apply ST_Plus2.  constructor. apply ST_PlusConstConst. 
  constructor.
Qed.

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t =>* t' /\ step_normal_form t').

Theorem normal_form_unique:
  deterministic normal_form_of.
Proof.
  (* We recommend using this initial setup as-is! *)
  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1.
  inversion P2 as [P21 P22]; clear P2.
  generalize dependent y2.
  induction P11.
  - intros. unfold step_normal_form in P12. destruct P21.
    + reflexivity.
    + unfold normal_form in P12. exfalso. apply P12. exists y. assumption.
  - intros. destruct P21.
    + exfalso. unfold step_normal_form in P22. unfold normal_form in P22. apply P22.
      exists y. assumption.
    + assert (y = y0). { apply step_deterministic with x; assumption. } subst.
      apply IHP11; assumption.
Qed.

Definition normalizing {X:Type} (R:relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 =>* t1' ->
     P t1 t2 =>* P t1' t2.
Proof.
  intros t1 t1' t2 H. induction H.
    - (* multi_refl *) apply multi_refl.
    - (* multi_step *) apply multi_step with (P y t2).
        apply ST_Plus1. apply H.
        apply IHmulti. Qed.

Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 =>* t2' ->
     P t1 t2 =>* P t1 t2'.
Proof.
  intros. induction H0.
  - constructor.
  - apply multi_step with (P t1 y).
    + constructor; assumption.
    + assumption.
Qed.

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  induction t.
  - exists (C n). split.
    + constructor.
    + rewrite nf_same_as_value. constructor.
  -       inversion IHt1 as [t1' H1]; clear IHt1.
      inversion IHt2 as [t2' H2]; clear IHt2.
      inversion H1 as [H11 H12]; clear H1. inversion H2 as [H21 H22]; clear H2.
      rewrite nf_same_as_value in H12. rewrite nf_same_as_value in H22.
      inversion H12 as [n1]. inversion H22 as [n2]. subst.
      exists (C (n1 + n2)). split.
     + assert (P t1 t2 =>* P (C n1) t2). {  apply multistep_congr_1. assumption. }
       assert (P (C n1) t2 =>* P (C n1) (C n2)). { apply multistep_congr_2; assumption. }
       assert (P t1 t2 =>* P (C n1) (C n2)). { apply multi_trans with (P (C n1) t2); assumption. }
       assert (P (C n1) (C n2) =>* C (n1 + n2)). {  apply multi_step with (C (n1 + n2)); constructor. } 
       apply multi_trans with (P (C n1) (C n2)); assumption.
     +  rewrite nf_same_as_value. constructor.
Qed.


Theorem eval__multistep: forall t n,
  t \\ n -> t =>* C n.
Proof.
  intros. induction H.
  - constructor.
  - assert (P t1 t2 =>* P (C n1) t2).  { apply multistep_congr_1. assumption. }
    assert (P (C n1) t2 =>* P (C n1) (C n2)). { apply multistep_congr_2. constructor. assumption. }
    assert (P t1 t2 =>* P (C n1) (C n2)). 
    {
      eapply multi_trans. apply H1. assumption.
    }
    eapply multi_trans. apply H3. apply multi_step with (C (n1 + n2)); constructor.
Qed.

Lemma step__eval : forall t t' n,
  t => t' ->
  t' \\ n ->
  t \\ n.
Proof.
  intros t t' n Hs. generalize dependent n. 
  induction Hs.
  - intros. inversion H. apply E_Plus; constructor.
  - intros. inversion H. subst. apply E_Plus. apply IHHs. assumption. assumption.
  - intros. inversion H0. subst. apply E_Plus. assumption. apply IHHs. assumption.
Qed.

Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t \\ n.
Proof.
  unfold normal_form_of. unfold step_normal_form. intros.
  destruct H. induction H.
  - apply nf_is_value in H0.  inversion H0. exists n. split. reflexivity. constructor.
  - apply IHmulti in H0. inversion H0. inversion H2. exists x0. split. assumption.
    apply step__eval with y; assumption.
Qed.

Theorem evalF_eval : forall t n,
  evalF t = n <-> t \\ n.
Proof.
  split.
  - intros. generalize dependent n. induction t.
    + intros. simpl in H. subst. constructor.
    + intros. simpl in H. remember (evalF t1) as n0. remember (evalF t2) as n1.
      rewrite <- H. assert (t1 \\ n0). { apply IHt1. reflexivity. } 
      assert (t2 \\ n1). { apply IHt2. reflexivity. }
      apply E_Plus; assumption.
  - intros. induction H.
    + reflexivity.
    + simpl. subst. reflexivity.
Qed.

Module Combined.

Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_true : value ttrue
  | v_false : value tfalse.

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
  | ST_IfTrue : forall t1 t2,
      tif ttrue t1 t2 => t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 => t2
  | ST_If : forall t1 t1' t2 t3,
      t1 => t1' ->
      tif t1 t2 t3 => tif t1' t2 t3

  where " t '=>' t' " := (step t t').

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try solve_by_invert; try reflexivity.
  -  apply IHHy1 in H2. rewrite H2. reflexivity.
  - destruct H1; inversion Hy1.
  - destruct H; inversion H3.
  - apply IHHy1 in H4. subst. reflexivity.
  - apply IHHy1 in H3. subst. reflexivity.
Qed.

Theorem not_strong_progress : exists t,
  ~(value t) /\ ~(exists t', t => t').
Proof.
  exists (P (C 0) ttrue). split.
  - unfold not. intros. inversion H.
  - unfold not. intros. inversion H. inversion H0.
    + inversion H4.
    + inversion H5.
Qed.

End Combined.