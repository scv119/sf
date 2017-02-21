Add LoadPath "/Users/chenshen/src/sf/".

Require Export IndProp.

Print ev.

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

Print ev_4.

Check (ev_SS 2 (ev_SS 0 ev_0)).

(* Construct proof object *)

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Print ev_4.
(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'.
(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4''.
(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'''.
(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)

Theorem ev_8 : ev 8.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_4.
Qed.

Definition ev_8' : ev 8 :=
  ev_SS 6 (ev_SS 4 (ev_4)).

Print ev_8'.
Print ev_8.

(* Prop <-> Type *)
(* Proof <-> Data value *)
(* as ev_8 is data value and ev 8 is data type *)

(* Proof as function *)
Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Print ev_plus4.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n: nat) => fun (H : ev n) =>
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4'.

Definition ev_plus4'' (n : nat) (H : ev n) : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''.

(* ev n is a dependent type *)

Definition ev_plus2 : Prop :=
  forall n, forall (E: ev n), ev (2 + n).

Print ev_plus2.

Definition  ev_plus2'' (n : nat) (H: ev n) : ev (2 + n) :=
  ev_SS n H.

Print ev_plus2.
Print ev_plus2''.

Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).

Print ev_plus2'.

(* P -> Q  is sytax suger for forall (_, P), Q *)

Module Props.

Module And.

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Print and.

End And.

Print prod.

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.

Definition and_comm'_aux P Q (H: P /\ Q) :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Check and_comm'_aux.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).


Definition conj_fact_aux1 P Q R (H: P /\ Q ) (H1: Q /\ R) :=
  match H with
  |  conj HP HQ => match H1 with
                   | conj HQ' HR => conj HP HR
                   end
  end.

Check conj_fact_aux1.

Definition conj_fact : forall  P Q R, P /\ Q -> Q /\ R -> P /\ R := conj_fact_aux1.

Module Or.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

End Or.

Definition or_aux P Q (H: P \/ Q) :=
  match H with
  | or_introl HP => or_intror HP
  | or_intror HQ => or_introl HQ
  end.

Check or_aux.

Definition or_comm : forall P Q, P \/ Q -> Q \/ P := or_aux.
  

Module Ex.

(* Amazing *)

Inductive ex {A : Type} (P : A -> Prop ) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

End Ex.

Check ex (fun n => ev n).

Definition some_nat_is_even : exists n, ev n :=
  ex_intro  ev 2  (ev_SS 0 ev_0).

Check some_nat_is_even.
Print some_nat_is_even.

Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).

Inductive True : Prop :=
  I : True.

Inductive False : Prop :=.

End Props.


Definition add1 : nat -> nat.
intros n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add1.

Compute add1 2.

Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

Notation "x = y" := (eq x y)
                    (at level 70, no associativity)
                     : type_scope.

Lemma leibniz_equality : forall (X: Type) (x y : X),
  x = y -> forall P: X -> Prop, P x -> P y.
Proof.
  intros X x y Eq H H1.  inversion Eq. rewrite <- H2. apply H1.
Qed.

Lemma four : 2 + 2 = 1 + 3.
Proof.
  apply eq_refl.
Qed.


Definition four' : 2 + 2 = 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Set) (x:X), []++[x] = x::[] :=
  fun (X:Set) (x:X) => eq_refl [x].

End MyEquality.

Definition quiz6 : exists x, x + 3 = 4 :=
  ex_intro (fun z => (z + 3 = 4)) 1 (refl_equal 4).