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