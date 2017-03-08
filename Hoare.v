Add LoadPath "/Users/chenshen/src/sf/".

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Imp.
Require Import Maps.

Definition Assertion := state -> Prop.

Module ExAssertions.
Definition as1 : Assertion := fun st => st X = 3.
(* state has st X equals 3 *)
Definition as2 : Assertion := fun st => st X <= st Y.
(* state has st X less or equal than st Y  *)
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
(* state has st X less or equal than st Y , or st X = 3 *)
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
(* any state *)
Definition as6 : Assertion := fun st => False.
(* none of the state *)
End ExAssertions.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.

Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* 
Hoare Triple:
"If command c is started in a state satisfying assertion P, and if c eventually terminates 
in some final state, then this final state will satisfy the assertion Q."
*)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
    c / st \\ st' ->
    P st ->
    Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_post_true : forall(P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros. unfold hoare_triple. intros. apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros. unfold hoare_triple. intros. exfalso. apply H in H1. assumption.
Qed.

(* Assignment rule:

{{ Q [X |-> a] }} X ::= a {{ Q }}

 To conclude that an arbitrary property Q holds after X ::= a, we need to assume that Q 
 holds before X ::= a, but with all occurrences of X replaced by a in Q. 

  where "Q [X |-> a]" is pronounced "Q where a is substituted for X".
*)

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (t_update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  intros. unfold hoare_triple. intros.
  inversion H. subst. unfold assn_sub in H0. assumption.
Qed.

Example assn_sub_example :
  {{(fun st => st X = 3) [X |-> ANum 3]}}
  (X ::= (ANum 3))
  {{fun st => st X = 3}}.
Proof.
  apply hoare_asgn. Qed.

Example assn_sub_ex1 :
  {{( fun st => st X <= 5 ) [X |-> APlus (AId X) (ANum 1)] }}
  (X ::= APlus (AId X) (ANum 1))
  {{ fun st => st X <= 5}}.
Proof.
  apply hoare_asgn. Qed.

Example assn_sub_ex2:
  {{(fun st => (0 <= (st X)) /\ (st X <= 5)) [ X |-> ANum 3]}}
  ( X::= ANum 3)
  {{ fun st => (0 <= (st X)) /\ (st X <= 5) }}.
Proof.
  apply hoare_asgn. Qed.

(* hoare_asgn_wrong  {{ True }} X::= a {{ X = a}} doesn't work for a = APlus (AId X) (ANum 10) *)

Lemma neq_refl: forall (X:Type) (x y:X),
  x <> y -> y <> x.
Proof.
  intros. intros H1. apply H. symmetry. assumption.
Qed.

Theorem hoare_asgn_fwd:
  (forall {X Y: Type} {f g : X -> Y},
    (forall (x :X), f x = g x) -> f = g) ->
  forall m a P,
  {{ fun st => P st /\ st X = m }}
    X ::= a
  {{ fun st => P (t_update st X m) /\ st X = aeval (t_update st X m) a }}.
Proof.
  intros. unfold hoare_triple. intros. inversion H1. inversion H0. subst.
  assert ( (t_update (t_update st X (aeval st a)) X (st X)) = st ). {
      apply H. intros. destruct (beq_id x X) eqn:Heqn.
      + apply beq_id_true_iff in Heqn. rewrite Heqn. apply t_update_eq.
      + apply beq_id_false_iff in Heqn.  
        assert ((t_update (t_update st X (aeval st a)) X (st X) x) = t_update st X (aeval st a) x). {
          apply t_update_neq. apply neq_refl. assumption.
        }
        rewrite H3. apply t_update_neq. apply neq_refl. assumption.
    }
   split.
  - rewrite H3. assumption.
  - rewrite H3. apply t_update_eq.
Qed.

Theorem hoare_asgn_fwd_exists :
  (forall {X Y: Type} {f g : X -> Y},
     (forall (x: X), f x = g x) -> f = g) ->
  forall a P,
  {{fun st => P st}}
    X ::= a
  {{fun st => exists m, P (t_update st X m) /\
                st X = aeval (t_update st X m) a }}.
Proof.
  intros functional_extensionality a P. unfold hoare_triple.
  intros. inversion H. subst. exists (st X).
  assert ( (t_update (t_update st X (aeval st a)) X (st X)) = st ). {
      apply functional_extensionality. intros. destruct (beq_id x X) eqn:Heqn.
      + apply beq_id_true_iff in Heqn. rewrite Heqn. apply t_update_eq.
      + apply beq_id_false_iff in Heqn.  
        assert ((t_update (t_update st X (aeval st a)) X (st X) x) = t_update st X (aeval st a) x). {
          apply t_update_neq. apply neq_refl. assumption.
        }
        rewrite H1. apply t_update_neq. apply neq_refl. assumption.
    }
  split.
  - rewrite H1. assumption.
  - rewrite H1. apply t_update_eq.
Qed. 


Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
    P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP.
  apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
    Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption. Qed.

Example hoare_asgn_example1 :
  {{fun st => True}} (X ::= (ANum 1)) {{fun st => st X = 1}}.
Proof.
  apply hoare_consequence_pre
    with (P' := (fun st => st X = 1) [X |-> ANum 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl. reflexivity.
Qed.