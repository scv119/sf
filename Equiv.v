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

Theorem IFB_true: forall b c1 c2,
     bequiv b BTrue ->
     cequiv
       (IFB b THEN c1 ELSE c2 FI)
       c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* b evaluates to true *)
      assumption.
    + (* b evaluates to false (contradiction) *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      inversion H5.
  - (* <- *)
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    rewrite Hb. reflexivity. Qed.

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

Lemma refl_aequiv : forall(a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity. Qed.

Lemma sym_aequiv : forall(a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H. Qed.

Lemma trans_aequiv : forall(a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity. Qed.

Lemma refl_bequiv : forall(b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity. Qed.

Lemma sym_bequiv : forall(b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H. Qed.

Lemma trans_bequiv : forall(b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity. Qed.

Lemma refl_cequiv : forall(c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. apply iff_refl. Qed.

Lemma sym_cequiv : forall(c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  assert (c1 / st \\ st' <-> c2 / st \\ st') as H'.
  { (* Proof of assertion *) apply H. }
  apply iff_sym. assumption.
Qed.


Lemma iff_trans : forall(P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros P1 P2 P3 H12 H23.
  inversion H12. inversion H23.
  split; intros A.
    apply H1. apply H. apply A.
    apply H0. apply H2. apply A. Qed.

Lemma trans_cequiv : forall(c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  apply iff_trans with (c2 / st \\ st'). apply H12. apply H23. Qed.


Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  intros i a1 a2 Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity. Qed.


Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  (* WORKED IN CLASS *)
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  - (* -> *)
    remember (WHILE b1 DO c1 END) as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileEnd *)
      apply E_WhileEnd. rewrite <- Hb1e. apply H.
    + (* E_WhileLoop *)
      apply E_WhileLoop with (st' := st').
      * (* show loop runs *) rewrite <- Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st'). apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity.
  - (* <- *)
    remember (WHILE b1' DO c1' END) as c'while
      eqn:Heqc'while.
    induction Hce; inversion Heqc'while; subst.
    + (* E_WhileEnd *)
      apply E_WhileEnd. rewrite -> Hb1e. apply H.
    + (* E_WhileLoop *)
      apply E_WhileLoop with (st' := st').
      * (* show loop runs *) rewrite -> Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st'). apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity. Qed.


Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
  unfold cequiv. intros.
  split; intros Hce. 
  - inversion Hce; subst.
    apply E_Seq with st'0. 
    + apply H. assumption.
    + apply H0. assumption.
  - inversion Hce; subst.
    apply E_Seq with st'0. 
    + apply H. assumption.
    + apply H0. assumption.
Qed.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI)
         (IFB b' THEN c1' ELSE c2' FI).
Proof.
  unfold bequiv, cequiv. intros.
  split; intros Hce.
  - inversion Hce. subst.
    + apply E_IfTrue. rewrite H in H7. assumption. apply H0 in H8. assumption.
    + apply E_IfFalse. rewrite H in H7. assumption. apply H1 in H8. assumption.
   - inversion Hce. subst.
    + apply E_IfTrue. rewrite <- H in H7. assumption. apply H0 in H8. assumption.
    + apply E_IfFalse. rewrite <- H in H7. assumption. apply H1 in H8. assumption.
Qed.
  

Example congruence_example:
  cequiv
    (* Program 1: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= ANum 0
     ELSE
       Y ::= ANum 42
     FI)
    (* Program 2: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= AMinus (AId X) (AId X) (* <--- changed here *)
     ELSE
       Y ::= ANum 42
     FI).
Proof.
  apply CSeq_congruence.
  apply refl_cequiv.
  apply CIf_congruence.
  apply refl_bequiv.
   apply CAss_congruence. unfold aequiv. simpl. symmetry. omega.
  apply refl_cequiv.
Qed.

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a: aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b: bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c: com),
    cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i => AId i
  | APlus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp
      (AMult (APlus (ANum 1) (ANum 2)) (AId X))
  = AMult (ANum 3) (AId X).
Proof. reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) =>
        if beq_nat n1 n2 then BTrue else BFalse
    | (a1', a2') =>
        BEq a1' a2'
    end
  | BLe a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) =>
        if leb n1 n2 then BTrue else BFalse
    | (a1', a2') =>
        BLe a1' a2'
    end
  | BNot b1 =>
    match (fold_constants_bexp b1) with
    | BTrue => BFalse
    | BFalse => BTrue
    | b1' => BNot b1'
    end
  | BAnd b1 b2 =>
    match (fold_constants_bexp b1, fold_constants_bexp b2)
    with
    | (BTrue, BTrue) => BTrue
    | (BTrue, BFalse) => BFalse
    | (BFalse, BTrue) => BFalse
    | (BFalse, BFalse) => BFalse
    | (b1', b2') => BAnd b1' b2'
    end
  end.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP =>
      SKIP
  | i ::= a =>
      CAss i (fold_constants_aexp a)
  | c1 ;; c2 =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.

Theorem fold_constants_aexp_sound:
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl; try reflexivity;
      try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.



Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* BTrue and BFalse are immediate *)
    try reflexivity.
  - (* BEq *) 
    rename a into a1. rename a0 into a2. simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    simpl. destruct (beq_nat n n0); reflexivity.
  - (* BLe *)
    simpl. 
    remember (fold_constants_aexp a) as a' eqn:Heqa.
    remember (fold_constants_aexp a0) as a0' eqn:Heqa0.
    replace (aeval st a) with (aeval st a') by 
        (subst a'; rewrite <-  fold_constants_aexp_sound; reflexivity).
    replace (aeval st a0) with (aeval st a0') by 
        (subst a0'; rewrite <-  fold_constants_aexp_sound; reflexivity).
    destruct a'; destruct a0'; try reflexivity.
    simpl. destruct (n <=? n0); reflexivity.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c. 
  induction c; simpl.
  - (* SKIP *) apply refl_cequiv.
  - (* ::= *) apply CAss_congruence.
              apply fold_constants_aexp_sound.
  - (* ;; *) apply CSeq_congruence; assumption.
  - (* IFB *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  - (* WHILE *)
       assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
      destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CWhile_congruence; assumption).
      + apply WHILE_true. assumption.
      + apply WHILE_false. assumption.
Qed.

Fixpoint optimize_0plus_aexp (e: aexp) : aexp :=
  match e with
  | AId i => AId i
  | ANum n =>
    ANum n
  | APlus (ANum 0) e2 =>
    optimize_0plus_aexp e2
  | APlus e1 e2 =>
    APlus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMinus e1 e2 =>
    AMinus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMult e1 e2 =>
    AMult (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
end.

Theorem optimize_0plus_aexp_sound : 
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. intros a.
  unfold aequiv. intros st.
  induction a; simpl; try reflexivity;
  destruct a1; destruct a2; try (destruct n); rewrite IHa1; rewrite IHa2; reflexivity.
Qed.

Fixpoint optimize_0plus_bexp (e: bexp) : bexp :=
  match e with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>  BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BLe a1 a2 =>  BLe (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BNot b1 => BNot (optimize_0plus_bexp b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_bexp b1) (optimize_0plus_bexp b2)
end.

Theorem optimize_0plus_bexp_sound : 
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. unfold bequiv. intros. 
  induction b; simpl; try reflexivity.
  - rewrite optimize_0plus_aexp_sound. assert (aeval st a0 = aeval st (optimize_0plus_aexp a0)). { apply optimize_0plus_aexp_sound. }
    rewrite H. reflexivity.
  - rewrite optimize_0plus_aexp_sound. assert (aeval st a0 = aeval st (optimize_0plus_aexp a0)). { apply optimize_0plus_aexp_sound. }
    rewrite H. reflexivity.
  - rewrite IHb. reflexivity.
  - rewrite IHb1, IHb2. reflexivity.
Qed.

Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | SKIP =>
      SKIP
  | i ::= a =>
      CAss i (optimize_0plus_aexp a)
  | c1 ;; c2 =>
      (optimize_0plus_com c1) ;; (optimize_0plus_com c2)
  | IFB b THEN c1 ELSE c2 FI => IFB (optimize_0plus_bexp b) THEN (optimize_0plus_com c1)
                     ELSE (optimize_0plus_com c2) FI
  | WHILE b DO c END =>
     WHILE (optimize_0plus_bexp b) DO (optimize_0plus_com c) END
  end.

Theorem optimize_0plus_com_sound :
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. unfold cequiv. intros c.
  induction c ; simpl; try reflexivity.
  - apply CAss_congruence. apply optimize_0plus_aexp_sound.
  - apply CSeq_congruence; assumption.
  - apply CIf_congruence; try apply optimize_0plus_bexp_sound; assumption.
  - apply CWhile_congruence; try apply optimize_0plus_bexp_sound; assumption.
Qed.

Definition double_optimize (c: com) : com :=
  optimize_0plus_com (fold_constants_com c).

Theorem double_optimize_sound :
  ctrans_sound double_optimize.
Proof.
  unfold ctrans_sound. unfold double_optimize.
  intros. apply trans_cequiv with (fold_constants_com c).
  apply fold_constants_com_sound.
  apply optimize_0plus_com_sound.
Qed.


Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | AId i' =>
      if beq_id i i' then u else AId i'
  | APlus a1 a2 =>
      APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2 =>
      AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.


Definition subst_equiv_property := forall i1 i2 a1 a2,
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

Theorem subst_inequiv : 
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra. 

  (* Here is the counterexample: assuming that subst_equiv_property
     holds allows us to prove that these two programs are
     equivalent... *)
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= AId X)
      as c1.
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= APlus (AId X) (ANum 1))
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).

  (* ... allows us to show that the command c2 can terminate
     in two different final states:
        st1 = {X |-> 1, Y |-> 1}
        st2 = {X |-> 1, Y |-> 2}. *)
  remember (t_update (t_update empty_state X 1) Y 1) as st1.
  remember (t_update (t_update empty_state X 1) Y 2) as st2.
  assert (H1: c1 / empty_state \\ st1);
  assert (H2: c2 / empty_state \\ st2);
  try (subst;
       apply E_Seq with (st' := (t_update empty_state X 1));
       apply E_Ass; reflexivity).
  apply H in H1.

  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
  assert (Hcontra: st1 = st2)
    by (apply (ceval_deterministic c2 empty_state); assumption).
  assert (Hcontra': st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'. Qed.

Inductive var_not_used_in_aexp (X:id) : aexp -> Prop :=
  | VNUNum: forall n, var_not_used_in_aexp X (ANum n)
  | VNUId: forall Y, X <> Y -> var_not_used_in_aexp X (AId Y)
  | VNUPlus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (APlus a1 a2)
  | VNUMinus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMinus a1 a2)
  | VNUMult: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMult a1 a2).

Lemma aeval_weakening : forall i st a ni,
  var_not_used_in_aexp i a ->
  aeval (t_update st i ni) a = aeval st a.
Proof.
  intros. induction H; try reflexivity;
    try (simpl; rewrite IHvar_not_used_in_aexp1; rewrite IHvar_not_used_in_aexp2; reflexivity).
  - simpl. unfold t_update. destruct beq_id eqn:Heqn.
    + exfalso. apply H. apply beq_id_true_iff. assumption.
    + reflexivity. unfold empty_state in H0.
Qed.


Theorem subst_equiv_property' : forall i1 i2 a1 a2,
  var_not_used_in_aexp i1 a1 ->
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).
Proof.
  intros. intros st st'. split.
  - intros H1. inversion H1. subst. apply E_Seq with st'0. assumption.  clear H1.  
    generalize dependent st'.
    generalize dependent st'0.    
    induction a2. 
    + intros. simpl. assumption.
    + intros. simpl. destruct (beq_id i1 i) eqn: Heqn.
      * simpl.  apply beq_id_true_iff in Heqn. subst i. inversion H3. subst.  remember (aeval st a1) as n.
        remember  ( t_update st i1 n) as st1.
        assert ( (i2 ::= AId i1) / st1 \\ t_update st1 i2 n). { apply E_Ass. rewrite Heqst1. simpl. apply t_update_eq. }
        assert (st' = t_update st1 i2 n) by (apply (ceval_deterministic (i2 ::= AId i1) st1); assumption).
        rewrite H1. apply E_Ass. rewrite Heqn. rewrite Heqst1. apply aeval_weakening. assumption.
      * simpl. assumption.
    + intros. simpl.  (* OH GOD *)
Admitted.

Theorem inequiv_exerices:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
  unfold cequiv. intros Contra.
  assert (SKIP / empty_state \\ empty_state). { apply E_Skip. }
  apply Contra in H. remember (WHILE BTrue DO SKIP END) as loop. 
  clear Contra. 
  induction H; inversion Heqloop.
  + subst. inversion H.
  + subst. apply IHceval2. reflexivity.
Qed.
  
    
Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com. (* <---- new *)

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' l" := (CHavoc l) (at level 60).

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st \\ st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
      aeval st a1 = n ->
      (X ::= a1) / st \\ t_update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = false ->
      c2 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
      beval st b1 = false -> 
      (WHILE b1 DO c1 END) / st \\ st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (WHILE b1 DO c1 END) / st' \\ st'' ->
      (WHILE b1 DO c1 END) / st \\ st''
  | E_Havoc : forall (st : state) (n : nat) (X : id),
      (HAVOC X) / st \\ t_update st X n

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

Example havoc_example1 : (HAVOC X) / empty_state \\ t_update empty_state X 0.
Proof.
apply E_Havoc.
Qed.

Example havoc_example2 :
  (SKIP;; HAVOC Z) / empty_state \\ t_update empty_state Z 42.
Proof.
apply E_Seq with empty_state; constructor. Qed.

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  c1 / st \\ st' <-> c2 / st \\ st'.

Definition pXY :=
  HAVOC X;; HAVOC Y.

Definition pYX :=
  HAVOC Y;; HAVOC X.

Theorem pXY_cequiv_pYX :
  cequiv pXY pYX.
Proof.
  unfold cequiv. intros st st''. split.
  - intros H. inversion H; subst. inversion H2. subst. inversion H5. subst.
    SearchAbout t_update. assert (X <> Y). { intros H'. inversion H'. }  apply t_update_permute with (X:=nat) (v1:=n0) (v2:=n) (m:=st) in H0 .
    rewrite H0. apply E_Seq with (t_update st Y n0); constructor.
  -  intros H. inversion H; subst. inversion H2. subst. inversion H5. subst.
    SearchAbout t_update. assert (X <> Y). { intros H'. inversion H'. }  apply t_update_permute with (X:=nat) (v1:=n) (v2:=n0) (m:=st) in H0 .
    rewrite <- H0. apply E_Seq with (t_update st X n0); constructor.
Qed.

Definition ptwice :=
  HAVOC X;; HAVOC Y.

Definition pcopy :=
  HAVOC X;; Y ::= AId X.

Lemma ptwice_cequiv_pcopy_lemma: forall A B a st st1 n,
  A<>B -> (A ::= a) / st \\ st1 -> st1 B = n -> st B = n.
Proof.
  intros. remember (A ::= a) as ass. induction H0; try inversion Heqass.
  subst. symmetry. apply t_update_neq. assumption.
Qed.

Lemma ptwice_cequiv_pcopy_lemma1: forall A B st st1 n,
  (A ::= AId B) / st \\ st1 -> st1 A = n -> st B = n.
Proof.
  intros. remember (A ::= AId B) as ass. induction H;try inversion Heqass. 
  subst. unfold aeval. symmetry.  apply t_update_eq.
Qed.

Theorem ptwice_cequiv_pcopy :
  ~cequiv ptwice pcopy.
Proof.
  unfold cequiv. intros Contra.
  assert (ptwice / empty_state \\ (t_update (t_update empty_state X 1) Y 2))
  by ( apply E_Seq with (t_update empty_state X 1); constructor ).
  apply Contra in H. clear Contra. inversion H. subst. 
  remember  ( t_update (t_update empty_state X 1) Y 2) as st.
  assert (X <> Y). { intros H'. inversion H'. }
  assert (Y <> X). { intros H'. inversion H'. }
  assert (st =  t_update (t_update empty_state Y 2) X 1). { rewrite Heqst. apply t_update_permute. assumption. }
  assert (st X = 1). { rewrite H3. apply t_update_eq. }
  assert (st Y = 2). { rewrite Heqst. apply t_update_eq. }
  assert (st' X = 1). { apply ptwice_cequiv_pcopy_lemma with (A:=Y) (a:=(AId X)) (st1:=st); assumption. }
  assert (st' X = 2). { apply ptwice_cequiv_pcopy_lemma1 with (A:=Y) (st1:=st); assumption. }
  rewrite  H7 in H8. inversion H8.
Qed.

Definition p1 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC Y;;
    X ::= APlus (AId X) (ANum 1)
  END.

Definition p2 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    SKIP
  END.

Lemma p1_may_diverge : forall st st', st X <>0 ->
  ~ p1 / st \\ st'.
Proof.
  intros. intros Contra. remember p1. induction Contra; subst; inversion Heqc.
  - rewrite H2 in H0. simpl in H0. rewrite negb_false_iff in H0. apply H. apply beq_nat_true in H0. assumption.
  - apply IHContra2. 
    + rewrite H3 in Contra1. inversion Contra1. subst. remember (st X) as m.
      assert (Y <> X). { intros H'. inversion H'. }
      assert (st'0 X  = m). { remember (HAVOC Y) as hav. induction H5; try inversion Heqhav. subst. apply t_update_neq; assumption. }
      assert (st' X = S m). { remember (X ::= APlus (AId X) (ANum 1)) as apl. induction H8; try inversion Heqapl. subst. simpl.
                              rewrite H2. SearchAbout plus. replace (st X + 1) with (S (st X)) by omega. apply t_update_eq. }
      rewrite H3. intros H'. inversion H'.
    + assumption.
Qed.

Lemma p2_may_diverge : forall st st', st X <>0 ->
  ~ p2 / st \\ st'.
Proof.
  intros. intros Contra. remember p2. induction Contra; subst; inversion Heqc.
  - rewrite H2 in H0. simpl in H0. rewrite negb_false_iff in H0. apply H. apply beq_nat_true in H0. assumption.
  - apply IHContra2. 
    + destruct Contra1; try inversion H3. assumption.
    + assumption.
Qed.
