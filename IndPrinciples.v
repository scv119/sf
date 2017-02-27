Add LoadPath "/Users/chenshen/src/sf/".
Require Export ProofObjects.

Check nat_ind.

Theorem mult_0_r' : forall n : nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros. assumption.
Qed.

Theorem plus_one_r' : forall n : nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros. simpl. rewrite H. reflexivity. Qed.

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.

Definition rbg_ind' : Prop := 
  forall P : rgb -> Prop, P red -> P green -> P blue -> forall r : rgb, P r.

Check rgb_ind.

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnocl : natlist1 -> nat -> natlist1.

Definition natlist1_ind' : Prop :=
  forall P : natlist1 -> Prop,
  P nnil1 ->
  (forall (l:natlist1), P l -> forall (n:nat), P (nsnocl l n)) ->
  forall n : natlist1, P n.

Check natlist1_ind.

Inductive byntree : Type :=
 | bempty : byntree
 | bleaf : yesno -> byntree
 | nbranch : yesno -> byntree -> byntree -> byntree.

Definition byntree_ind' : Prop :=
  forall P : byntree -> Prop,
  P bempty ->
  (forall (y:yesno), P (bleaf y)) ->
  (forall (b1:byntree), P b1 -> forall (b2:byntree), P b2 -> forall (y:yesno), P (nbranch y b1 b2)) ->
  forall b : byntree, P b.

Check byntree_ind.

Inductive ExSet : Type :=
  | conl : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet.

Check ExSet_ind.

Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.

Definition tree_ind' : Prop :=
  forall (X : Type) (P : (tree X) -> Prop),
  forall (x : X), P (leaf X x) ->
  (forall (t : tree X), P t -> forall (t1 : tree X), P t1 -> P (node X t t1)) ->
  forall t : tree X, P t.

Check tree_ind.

Inductive mytype (X:Type) : Type :=
  | constr1 : X -> mytype X 
  | constr2 : nat -> mytype X 
  | constr3 : mytype X -> nat -> mytype X.

Check mytype_ind.

Inductive foo (X:Type) (Y:Type) : Type :=
  | bar : X -> foo X Y
  | baz : Y -> foo X Y
  | quux : (nat -> foo X Y) -> foo X Y.

Check foo_ind.

Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.

Definition foo'_ind' : Prop :=
  forall (X : Type) (P : foo' X -> Prop),
  (forall (l : list X) (f : foo' X), P f ->  P (C1 X l f)) ->
  P (C2 X) ->
  forall f : foo' X, P f.

Check foo'_ind.
