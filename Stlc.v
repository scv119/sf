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
