Add LoadPath "/Users/chenshen/src/sf/".
Require Import Coq.omega.Omega.
Require Import Maps.
Require Import Imp.

Ltac inv H := inversion H; subst; clear H.

Theorem ceval_deterministic: forall c st st1 st2,
     c / st \\ st1 ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2. 
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
  - (* b evaluates to true *)
    apply IHE1. assumption.
  - (* b evaluates to false (contradiction) *)
    rewrite H in H5. inversion H5.
  (* E_IfFalse *)
  - (* b evaluates to true (contradiction) *)
    rewrite H in H5. inversion H5.
  - (* b evaluates to false *)
    apply IHE1. assumption.
  (* E_WhileEnd *)
  - (* b evaluates to false *)
    reflexivity.
  - (* b evaluates to true (contradiction) *)
    rewrite H in H2. inversion H2.
  (* E_WhileLoop *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption. Qed.

Example auto_example_1 : forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. assumption.
Qed.

Example auto_example_1' : forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  auto.
Qed.

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P->Q) -> (P->S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

Example auto_example_3 : forall (P Q R S T U: Prop),
                           (P -> Q) -> (Q -> R) -> (R -> S) ->
                           (S -> T) -> (T -> U) -> P -> U.
Proof.
  (* When it cannot solve the goal, auto does nothing *)
  auto.
  (* Optional argument says how deep to search (default depth is 5) *)
  auto 6.
Qed.

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  auto. Qed.


Example auto_example_5: 2 = 2.
Proof.
  (* auto subsumes reflexivity because eq_refl is in hint database *)
  info_auto.
Qed.


Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. omega. Qed.

Example auto_example_6 : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto. (* does nothing: auto doesn't destruct hypotheses! *)
  auto using le_antisym.
Qed.

Hint Resolve le_antisym.

Example auto_example_6' : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto. 
Qed.


Definition is_fortytwo x := x = 42.

Example auto_example_7: forall x, (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto. (* does nothing *)
Abort.

Hint Unfold is_fortytwo.

Example auto_example_7' : forall x, (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  info_auto.
Qed.

Hint Constructors ceval.
Hint Transparent state.
Hint Transparent total_map.

Definition st12 := t_update (t_update empty_state X 1) Y 2.
Definition st21 := t_update (t_update empty_state X 2) Y 1.

Example auto_example_8 : exists s',
  (IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI) / st21 \\ s'.
Proof. eauto. Qed.

Example auto_example_8' : exists s',
  (IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI) / st12 \\ s'.
Proof. info_eauto. Qed.
