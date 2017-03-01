Add LoadPath "/Users/chenshen/src/sf/".


Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import Maps.
Require Import Imp.


Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st: state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st \\ st') <->  (c2 / st \\st').

Definition prog_a : com :=
  WHILE BNot (BLe (AId X) (ANum 0)) DO
    X ::= APlus (AId X) (ANum 1)
  END.

Definition prog_b : com :=
  IFB BEq (AId X) (ANum 0) THEN
    X ::= APlus (AId X) (ANum 1);;
    Y ::= ANum 1
  ELSE
    Y ::= ANum 0
  FI;;
  X ::= AMinus (AId X) (AId Y);;
  Y ::= ANum 0.

Definition prog_c : com :=
  SKIP.

Definition prog_d : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= APlus (AMult (AId X) (AId Y)) (ANum 1)
  END.

Definition prog_e : com :=
  Y ::= ANum 0.

Definition prog_f : com :=
  Y ::= APlus (AId X) (ANum 1);;
  WHILE BNot (BEq (AId X) (AId Y)) DO
    Y ::= APlus (AId X) (ANum 1)
  END.

Definition prog_g : com :=
  WHILE BTrue DO
    SKIP
  END.

Definition prog_h : com :=
  WHILE BNot (BEq (AId X) (AId X)) DO
    X ::= APlus (AId X) (ANum 1)
  END.

Definition prog_i : com :=
  WHILE BNot (BEq (AId X) (AId Y)) DO
    X ::= APlus (AId Y) (ANum 1)
  END.

Definition equiv_classes : list (list com) 
  (* REPLACE THIS LINE WITH   := _your_definition_ . *) . Admitted.

Theorem aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
  intros st. simpl. omega.
Qed.

Theorem bequiv_example:
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

Theorem skip_left: forall c,
  cequiv
     (SKIP;; c)
     c.
Proof.
  (* WORKED IN CLASS *)
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H. subst.
    inversion H2. subst.
    assumption.
  - (* <- *)
    apply E_Seq with st. 
    apply E_Skip.
    assumption.
Qed.

Theorem skip_right : forall c,
  cequiv (c ;; SKIP) c.
Proof.
  intros c st st'.
  split; intros H.
  - inversion H. subst.
    inversion H5. subst. assumption.
  - apply E_Seq with st'.
    assumption. constructor.
Qed.

Theorem IFB_true_simple: forall c1 c2,
  cequiv
    (IFB BTrue THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  - (* -> *)
    inversion H; subst. assumption. inversion H5.
  - (* <- *)
    apply E_IfTrue. reflexivity. assumption. Qed.

Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse ->
  cequiv (IFB b THEN c1 ELSE c2 FI)
  c2.
Proof.
  intros b c1 c2 H.
  split; intros H1.
  - inversion H1; subst.
    + unfold bequiv in H. simpl in H. rewrite H in H6. inversion H6.
    + assumption.
  - unfold bequiv in H. simpl in H. apply E_IfFalse. apply H. apply H1. Qed.

Theorem swap_if_branches : forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros b e1 e2 st st'. split; intros H. 
  - inversion H; subst.
    + apply E_IfFalse. 
      * simpl. rewrite H5. reflexivity.
      * assumption.
    + apply E_IfTrue.
      * simpl. rewrite H5. reflexivity.
      * assumption.
  - inversion H; subst; simpl in H5. apply negb_true_iff in H5.
    + apply E_IfFalse; assumption.
    + apply E_IfTrue;  apply negb_false_iff in H5; assumption.
Qed.

Theorem WHILE_false : forall b c,
     bequiv b BFalse ->
     cequiv
       (WHILE b DO c END)
       SKIP.
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* E_WhileEnd *)
      apply E_Skip.
    + (* E_WhileLoop *)
      rewrite Hb in H2. inversion H2.
  - (* <- *)
    inversion H; subst.
    apply E_WhileEnd.
    rewrite Hb.
    reflexivity. Qed.

(* Theorem If b is equivalance to BFalse, then (WHILE b DO c END) is equivalent to SKIP 
  Proof.
    . -> we must show for all st and st', that (WHILE b DO c END) / st \\ st' then SKIP / st \\ st'
         Proceed by case on the rules that could possible have been used to show (WHILE b DO c END) / st \\ st ',
         namely E_WhileEnd and E_WhileLoop.
        
         Suppose the rule in the dervation was E_WhileEnd. We then have , by the premises of E_WhileEnd, that 
         st = st', which could be only possible rule to show SKIP / st \\ st' as well.
        
         Suppose the rule is E_WhileLoop, then we ahve beval st b = true, which by replacing bequiv b BFalse, we have 
         beval st BFalse = true, which contradict to beval's definition.
    
      <- We must show for all st and st', that SKIP / st \\ st' then  (WHILE b DO c END) / st \\ st'.
         Process by case on the rule that only possbiel rule is that st = st'. And by applying E_WhileEnd we 
          need to show:  beval b = false and st = st'. By replace our premise we could have beval Bfalse = false.
            ...

*)

Lemma WHILE_true_nonterm : forall b c st st',
     bequiv b BTrue ->
     ~( (WHILE b DO c END) / st \\ st' ).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  induction H;
    (* Most rules don't apply, and we can rule them out
       by inversion *)
    inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for WHILE loops: *)
  - (* E_WhileEnd *) (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* rewrite is able to instantiate the quantifier in st *)
    rewrite Hb in H. inversion H.
  - (* E_WhileLoop *) (* immediate from the IH *)
    apply IHceval2. reflexivity. Qed.

Theorem WHILE_true: forall b c,
     bequiv b BTrue ->
     cequiv
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof.
  intros b c Hb st st'. split; intros H.
  - exfalso. apply WHILE_true_nonterm with (c:=c) (st:=st) (st':=st')  in Hb. apply Hb. assumption.
  - exfalso. assert (Hb':bequiv BTrue BTrue). { unfold bequiv. intros. reflexivity. }
    apply WHILE_true_nonterm with (c:=SKIP) (st:=st) (st':=st')  in Hb'. apply Hb'. assumption.
Qed.

Theorem loop_unrolling: forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  intros b c st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* loop doesn't run *)
      apply E_IfFalse. assumption. apply E_Skip.
    + (* loop runs *)
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  - (* <- *)
    inversion Hce; subst.
    + (* loop runs *)
      inversion H5; subst.
      apply E_WhileLoop with (st' := st'0).
      assumption. assumption. assumption.
    + (* loop doesn't run *)
      inversion H5; subst. apply E_WhileEnd. assumption. Qed.

Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  intros. intros st st'. split; intros H.
  - inversion H; subst.
    inversion H2; subst.
    apply E_Seq with (st':=st'1). assumption.
    apply E_Seq with (st':=st'0); assumption.
  - inversion H; subst.
    inversion H5; subst.
    apply E_Seq with (st':=st'1).
    apply E_Seq with (st':=st'0). assumption.
    assumption. assumption.
Qed.

Theorem identity_assignment : forall (X:id),
  cequiv
    (X ::= AId X)
    SKIP.
Proof.
   intros. split; intro H.
     - (* -> *)
       inversion H; subst. simpl.
       replace (t_update st X (st X)) with st.
       + constructor.
       + apply functional_extensionality. intro.
         rewrite t_update_same; reflexivity.
     - (* <- *) 
       replace st' with (t_update st' X (aeval st' (AId X))).
       + inversion H. subst. apply E_Ass. reflexivity.
       + apply functional_extensionality. intro.
         rewrite t_update_same. reflexivity.
Qed.

Theorem assign_aequiv : forall X e,
  aequiv (AId X) e ->
  cequiv SKIP (X ::= e).
Proof.
  intros. split; intro H1.
  - replace st' with (t_update st' X (aeval st e)); inversion H1; subst.
    +  apply E_Ass. reflexivity.
    + apply functional_extensionality. intro. unfold aequiv in H. rewrite <- H.
      rewrite t_update_same. reflexivity.
  -  inversion H1; subst. replace ( t_update st X (aeval st e) ) with st.
    + constructor.
    + rewrite <- H. rewrite t_update_same. reflexivity.
Qed.
