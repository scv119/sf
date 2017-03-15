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

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros. apply hoare_consequence_post with Q'.
  + apply hoare_consequence_pre with P'; assumption.
  + assumption.
Qed.

Example hoare_asgn_example1' :
  {{fun st => True}}
  (X ::= (ANum 1))
  {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre. 
  apply hoare_asgn.
  intros st H.  reflexivity. Qed.

Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. apply HP.
Abort.

Lemma silly2 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. destruct HP as [y HP'].
Abort.

Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
   intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. apply HP'.
Qed.

Lemma silly2_eassumption :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
   intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

Example assn_sub_ex1' :
  {{ fun st => st X + 1 <= 5 }}
  ( X ::= APlus (AId X) (ANum 1) )
  {{ fun st => st X <= 5 }}.
Proof.
  intros. eapply hoare_consequence_pre. apply hoare_asgn.
  intros st H. unfold assn_sub. simpl. rewrite t_update_eq. assumption.
Qed.

Example assn_sub_ex2' :
  {{ fun st => 0 <= 3 /\ 3 <= 5 }}
  ( X ::= ANum 3 )
  {{ fun st => 0 <= st X  /\ st X <= 5 }}.
Proof.
  intros. eapply hoare_consequence_pre. apply hoare_asgn.
  intros st H. unfold assn_sub. simpl. rewrite t_update_eq. assumption.
Qed.


Theorem hoare_skip : forall P,
  {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}}
  (X ::= a;; SKIP)
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - (* right part of seq *)
    apply hoare_skip.
  - (* left part of seq *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. subst. reflexivity.
Qed.

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2))
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
   eapply hoare_seq. apply hoare_asgn. 
   eapply hoare_consequence_pre. apply hoare_asgn.
   intros st H. unfold assn_sub. simpl. split; unfold t_update; reflexivity.
Qed.

Definition swap_program : com :=
  Z::= (AId X) ;; X ::= (AId Y) ;; Y ::= (AId Z).

Theorem swap_excerice :
 {{fun st => st X <= st Y }}
  swap_program 
 {{fun st => st Y <= st X }}.
Proof.
  apply hoare_seq with (fun st => st X <= st Y /\ st Z <= st Y ).
  + eapply hoare_seq. apply  hoare_asgn.
   eapply hoare_consequence_pre. apply hoare_asgn. intros st H. unfold assn_sub. simpl.
   rewrite t_update_eq. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_eq.
  inversion H. assumption. intros H'. inversion H'. intros H'. inversion H'.
  + eapply hoare_consequence_pre. apply hoare_asgn. intros st H. unfold assn_sub.  simpl. split.
    - repeat rewrite t_update_neq. assumption. intros H'. inversion H'. intros H'. inversion H'.
    - rewrite t_update_eq. rewrite t_update_neq. assumption. intros H'. inversion H'.
Qed.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros. unfold bassn. assumption.
Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros. unfold bassn. intros H'. rewrite H in H'. inversion H'.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{ fun st => P st /\ bassn b st }} c1 {{ Q }} ->
  {{ fun st => P st /\ ~ (bassn b st) }} c2 {{ Q }} ->
  {{ P }} (IFB b THEN c1 ELSE c2 FI) {{ Q }}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
      assumption.
      split. assumption.
             apply bexp_eval_true. assumption.
  - (* b is false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
             apply bexp_eval_false. assumption. Qed.

Example if_example :
    {{fun st => True}}
  IFB (BEq (AId X) (ANum 0))
    THEN (Y ::= (ANum 2))
    ELSE (Y ::= APlus (AId X) (ANum 1))
  FI
    {{fun st =>st X <= st Y}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre. apply hoare_asgn. unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros. inversion H. apply beq_nat_true in H1. rewrite H1. omega.
  -  eapply hoare_consequence_pre. apply hoare_asgn. unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros. omega.
Qed.

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
  apply hoare_if. 
  - eapply hoare_consequence_pre. apply hoare_asgn. unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros. inversion H. SearchAbout le. apply  leb_complete in H1. symmetry. apply le_plus_minus_r. assumption.
  - eapply hoare_consequence_pre. apply hoare_asgn. unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros. reflexivity.
Qed.


Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'IF1' b 'THEN' c 'FI'" :=
  (CIf1 b c) (at level 80, right associativity).

Reserved Notation "c1 '/' st '\\' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip :  forall st : state, SKIP / st \\ st
  | E_Ass :  forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st \\ t_update st X n
  | E_Seq :  forall (c1 c2 : com) (st st' st'' : state),
            c1 / st \\ st' -> c2 / st' \\ st'' -> (c1 ;; c2) / st \\ st''
  | E_IfTrue :  forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse :  forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd :  forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st \\ st
  | E_WhileLoop :  forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st \\ st' ->
                  (WHILE b1 DO c1 END) / st' \\ st'' ->
                  (WHILE b1 DO c1 END) / st \\ st''
  | E_If1True: forall (st st' : state) (b1 : bexp) (c1 : com),
               beval st b1 = true ->
               c1 / st \\ st' -> (IF1 b1 THEN c1 FI) / st \\ st'
  | E_If1False: forall (st : state) (b1 : bexp) (c1 : com),
               beval st b1 = false ->  (IF1 b1 THEN c1 FI) / st \\ st

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
   forall st st',
       c / st \\ st' ->
       P st ->
       Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level)
                                  : hoare_spec_scope.

Theorem hoare_if1 : forall P Q b c,
  {{ fun st => P st /\ bassn b st }} c {{ Q }} ->
  {{ fun st => P st /\ ~ (bassn b st) }} SKIP {{ Q }} ->
  {{ P }} (IF1 b THEN c FI) {{ Q }}.
Proof.
   intros P Q b c HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - apply (HTrue st st'). assumption. split; assumption.
  - apply (HFalse st' st'). apply E_Skip. split. assumption. intros H. unfold bassn in H. rewrite H3 in H.
    inversion H.
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

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  intros. unfold hoare_triple. intros.
  inversion H. subst. unfold assn_sub in H0. assumption.
Qed.

Theorem hoare_skip : forall P,
  {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst. assumption.
Qed.

Lemma hoare_if1_good :
  {{ fun st => st X + st Y = st Z }}
  IF1 BNot (BEq (AId Y) (ANum 0)) THEN
    X ::= APlus (AId X) (AId Y)
  FI
  {{ fun st => st X = st Z }}.
Proof. 
  apply hoare_if1.
  - eapply hoare_consequence_pre. apply hoare_asgn. unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros. inversion H. assumption.
  - eapply hoare_consequence_pre. apply hoare_skip. unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros. inversion H. apply eq_true_negb_classical in H1. apply beq_nat_true in H1. rewrite H1 in H0.
    simpl in H0. rewrite <- plus_n_O in H0. assumption.
Qed.

End If1.

Lemma hoare_while: forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hoare st st' He Hp.
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - split. assumption. apply bexp_eval_false. assumption.
  - apply IHHe2. reflexivity. apply (Hoare st st'). assumption. split. assumption. apply bexp_eval_true. assumption.
Qed.


Example while_example :
    {{fun st => st X <= 3}}
  WHILE (BLe (AId X) (ANum 2))
  DO X ::= APlus (AId X) (ANum 1) END
    {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post. 
  apply hoare_while.
  eapply  hoare_consequence_pre.
  apply hoare_asgn.
  unfold bassn, assn_sub, assert_implies, t_update. simpl.
  intros st [H1 H2]. apply leb_complete in H2. omega.
   unfold bassn, assn_sub, assert_implies, t_update. intros st [Hle Hb].
    simpl in Hb. destruct (leb (st X) 2) eqn: Heqle.
    exfalso. apply Hb. reflexivity.
    apply leb_iff_conv in Heqle. omega.
Qed.

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{ Q }}.
Proof.
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  - apply hoare_post_true. intros st. apply I.
  - simpl. intros st [H1 H2]. exfalso. apply H2. unfold bassn. reflexivity.
  - unfold assert_implies. intros. apply I.
Qed.

Module RepeatExercise.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e1 b2) (at level 80, right associativity).

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (t_update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ;; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
  | E_RepeatEnd : forall st st' b1 c1,
      ceval st c1 st' ->
      beval st' b1 = true ->
      ceval st (REPEAT c1 UNTIL b1 END) st'
  | E_RepeatLoop : forall st st' st'' b1 c1,
      ceval st c1 st' ->
      beval st' b1 = false ->
      ceval st' (REPEAT c1 UNTIL b1 END) st'' ->
      ceval st (REPEAT c1 UNTIL b1 END) st''
.

Notation "c1 '/' st '\\' st'" := (ceval st c1 st')
                                 (at level 40, st at level 39).

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion)
                        : Prop :=
  forall st st', (c / st \\ st') -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

Definition ex1_repeat :=
  REPEAT
    X ::= ANum 1;;
    Y ::= APlus (AId Y) (ANum 1)
  UNTIL (BEq (AId X) (ANum 1)) END.

Theorem ex1_repeat_works :
  ex1_repeat / empty_state \\
               t_update (t_update empty_state X 1) Y 1.
Proof.
  apply E_RepeatEnd.
  - apply E_Seq with (t_update empty_state X 1).
    + apply E_Ass. reflexivity.
    + apply E_Ass. reflexivity.
  - reflexivity.
Qed.

Lemma hoare_repeat : forall P Q b c,
  {{fun st => Q st /\ ~ bassn b st}} c {{Q}} ->
  {{P}} c {{Q}} ->
  {{P}} REPEAT c UNTIL b END {{fun st => Q st /\ bassn b st}}.
Proof.
  unfold hoare_triple; intros. generalize dependent P.
  remember (REPEAT c UNTIL b END) as loopdef eqn:loop.
  induction H1; inversion loop; subst.
  - intros. subst. split. eapply H2. apply H1. assumption. unfold bassn. assumption.
  - intros. subst. eapply IHceval2.
    + subst. reflexivity.
    + eapply H.
    + simpl. split.
     * eapply H1. eassumption. assumption.
     * intros H3. unfold bassn in H3. rewrite H0 in H3. inversion H3.
Qed.

End RepeatExercise.

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' X" := (CHavoc X) (at level 60).

Reserved Notation "c1 '/' st '\\' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st \\ st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st \\ t_update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st \\ st' -> c2 / st' \\ st'' -> (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st \\ st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st \\ st' ->
                  (WHILE b1 DO c1 END) / st' \\ st'' ->
                  (WHILE b1 DO c1 END) / st \\ st''
  | E_Havoc : forall (st : state) (X : id) (n : nat),
              (HAVOC X) / st \\ t_update st X n

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', c / st \\ st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level)
                                  : hoare_spec_scope.

Definition havoc_pre (X : id) (Q : Assertion) : Assertion :=
  fun st => (forall x, Q (t_update st X x)).

Theorem hoare_havoc : forall (Q : Assertion) (X : id),
  {{ havoc_pre X Q }} HAVOC X {{ Q }}.
Proof.
  intros. intros st st'. intros H. remember (HAVOC X) as havoc.
  destruct H; try inversion Heqhavoc. intros. unfold havoc_pre in H. apply H.
Qed.

End Himp.