Add LoadPath "/Users/chenshen/src/sf/".

Require Export IndProp.

Definition relation (X: Type) := X -> X -> Prop.

Print le.

Check le : nat -> nat -> Prop.

Check le : relation nat.

(* Partial Functions *)

Definition partial_function {X : Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Print next_nat.