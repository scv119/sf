Add LoadPath "/Users/chenshen/src/sf/".


Require Import Maps.
Require Import Smallstep.
Require Import Types.



Module STLC.

Inductive ty : Type :=
  | TBool : ty
  | TArrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.


Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

(** [idB = \x:Bool. x] *)

Notation idB :=
  (tabs x TBool (tvar x)).

(** [idBB = \x:Bool->Bool. x] *)

Notation idBB :=
  (tabs x (TArrow TBool TBool) (tvar x)).

(** [idBBBB = \x:(Bool->Bool) -> (Bool->Bool). x] *)

Notation idBBBB :=
  (tabs x (TArrow (TArrow TBool TBool)
                      (TArrow TBool TBool))
    (tvar x)).

(** [k = \x:Bool. \y:Bool. x] *)

Notation k := (tabs x TBool (tabs y TBool (tvar x))).

(** [notB = \x:Bool. if x then false else true] *)

Notation notB := (tabs x TBool (tif (tvar x) tfalse ttrue)).

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_true :
      value ttrue
  | v_false :
      value tfalse.

Hint Constructors value.

Fixpoint test1 (n :nat) : nat :=
  match n with 
  | O => if Nat.eqb n n then 1 else 2
  | _ => n
  end.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' =>
      if beq_id x x' then s else t
  | tabs x' T t1 =>
      tabs x' T (if beq_id x x' then t1 else ([x:=s] t1))
  | tapp t1 t2 =>
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttrue =>
      ttrue
  | tfalse =>
      tfalse
  | tif t1 t2 t3 =>
      tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Inductive substi (s:tm) (x:id) : tm -> tm -> Prop :=
  | s_var1 :
    substi s x (tvar x) s
  | s_var2 : forall (y: id), 
    x <> y -> substi s x (tvar y) (tvar y)
  | s_abs1 : forall T t1,
    substi s x (tabs x T t1) (tabs x T t1)
  | s_abs2 : forall y T t1 t2,
    x <> y -> 
    substi s x t1 t2 ->
    substi s x (tabs y T t1) (tabs y T t2)
  | s_tapp : forall t1 t1' t2 t2',
    substi s x t1 t1' ->
    substi s x t2 t2' ->
    substi s x (tapp t1 t2) (tapp t1' t2')
  | s_ttrue :
    substi s x ttrue ttrue
  | s_ttfalse :
    substi s x tfalse tfalse
  | s_tif : forall t1 t1' t2 t2' t3 t3',
    substi s x t1 t1' ->
    substi s x t2 t2' ->
    substi s x t3 t3' ->
    substi s x (tif t1 t2 t3) (tif t1' t2' t3').

Hint Constructors substi.
Hint Resolve beq_id_true_iff.
Hint Resolve beq_id_false_iff.
Hint Resolve beq_id_refl.

Theorem substi_correct : forall s x t t',
  [x:=s]t = t' <-> substi s x t t'.
Proof with auto.
  split.
  - intros. generalize dependent t'. induction t; intros t' H; simpl in H; subst; auto.
    + destruct (beq_id x0 i) eqn:Heq.
      * apply beq_id_true_iff in Heq. subst. auto.
      * apply beq_id_false_iff in Heq. subst. auto.
    + destruct (beq_id x0 i) eqn:Heq.
      * apply beq_id_true_iff in Heq. subst. auto.
      * apply beq_id_false_iff in Heq. subst. auto.
  - intros H. induction H; simpl; try (rewrite <- beq_id_refl); 
    try (apply beq_id_false_iff in H; rewrite H); subst; auto.
Qed.


Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         tapp v1 t2 ==> tapp v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)

where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Lemma step_example1 :
  (tapp idBB idB) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl. Qed.



Lemma step_example5 :
       (tapp (tapp idBBBB idBB) idB)
  ==>* idB.
Proof.
  eapply multi_step.
    apply ST_App1.
    apply ST_AppAbs. constructor. simpl.
  eapply multi_step.
    apply ST_AppAbs. constructor. simpl.
  constructor.
Qed.

Lemma step_example5_with_normalize :
       (tapp (tapp idBBBB idBB) idB)
  ==>* idB.
Proof. normalize. Qed.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      update Gamma x T11 |- t12 \in T12 ->
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 ->
      Gamma |- t2 \in T11 ->
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.


Example typing_example_1 :
  empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
Proof.
  apply T_Abs. apply T_Var. reflexivity. Qed. 

Example typing_example_3 :
  exists T,
    empty |-
      (tabs x (TArrow TBool TBool)
         (tabs y (TArrow TBool TBool)
            (tabs z TBool
               (tapp (tvar y) (tapp (tvar x) (tvar z)))))) \in
      T.
Proof with auto.
  exists (TArrow (TArrow TBool TBool) (TArrow (TArrow TBool TBool) (TArrow TBool TBool))).
  apply T_Abs.
  apply T_Abs.
  apply T_Abs.
  eapply T_App. apply T_Var. reflexivity.
  eapply T_App. apply T_Var. reflexivity.
  apply T_Var. reflexivity.
Qed.

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |-
          (tabs x S
             (tapp (tvar x) (tvar x))) \in
          T).
Proof.
  unfold not. intros. inversion H. clear H. inversion H0. clear H0.
  inversion H. subst. clear H. inversion H5. subst. clear H5. inversion H2. subst. clear H2.
  inversion H4. subst. clear H4. rewrite -> H2 in H1. inversion H1. clear H1. clear H2.
  generalize dependent T12. induction T11.
  + intros. inversion H0.
  + intros. inversion H0. apply IHT11_1 with T11_2. auto.
Qed.

End STLC.