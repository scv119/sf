Add LoadPath "/Users/chenshen/src/sf/".

Require Import Maps.
Require Import Types.
Require Import Stlc.
Require Import Smallstep.
Module STLCProp.
Import STLC.

Lemma canonical_form_bool : forall t, 
  empty |- t \in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.


Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x0. exists t0. auto.
Qed.
