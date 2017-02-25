Add LoadPath "/Users/chenshen/src/sf/".

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.

Module AExp.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(*
BNF: 
    a ::= nat
        | a + a
        | a - a
        | a * a

    b ::= true
        | false
        | a = a
        | a ≤ a
        | not b
        | b and b

*)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum a => a
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Fixpoint beval (a : bexp) : bool :=
  match a with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2 => leb (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound : forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - reflexivity.
  - destruct a1.
    + destruct n.
      * simpl. apply IHa2.
      * simpl. rewrite IHa2. reflexivity.
    + simpl. rewrite IHa2. simpl in IHa1. rewrite IHa1. reflexivity.
    + simpl. rewrite IHa2. simpl in IHa1. rewrite IHa1. reflexivity.
    + simpl. rewrite IHa2. simpl in IHa1. rewrite IHa1. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. (* this just does reflexivity *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* just reflexivity would have failed *)
  apply HP. (* we can still finish the proof in some other way *)
Qed.

Lemma foo' : forall n, leb 0 n = true.
Proof.
  intros.
  (* destruct the current goal *)
  destruct n; 
  (* then simpl each resulting subgoal *)
  simpl; 
  (* and do reflexivity on each resulting subgoal *)
  reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... but the remaining cases -- ANum and APlus -- 
       are different: *)
    try reflexivity.
  - (* APlus *)
    destruct a1;
      (* Again, most cases follow directly by the IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* The interesting case, on which the try...
       does nothing, is when e1 = ANum n. In this
       case, we have to destruct n (to see whether
       the optimization applies) and rewrite with the
       induction hypothesis. *)
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue => b
  | BFalse => b
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot _ => b
  | BAnd _ _ => b
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros b;
  induction b;
    try (simpl; reflexivity);
    simpl; repeat (rewrite optimize_0plus_sound'); reflexivity.
Qed.


Fixpoint optimize_0 (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0 e2
  | APlus e1 e2 => APlus (optimize_0 e1) (optimize_0 e2)
  | AMinus e1 (ANum 0) => optimize_0 e1
  | AMinus e1 e2 => AMinus (optimize_0 e1) (optimize_0 e2)
  | AMult (ANum 0) _ => ANum 0
  | AMult e1 e2 => AMult (optimize_0 e1) (optimize_0 e2)
  end.

Lemma sound_lemma : forall a,
  a - 0 = a.
Proof.
  destruct a; simpl; reflexivity.
Qed.

Theorem optimize_0_sound : forall a,
  aeval (optimize_0 a) = aeval a.
Proof.
  intros a.
  induction a;
    try (simpl; reflexivity).
  - destruct a1;
    try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    + destruct n ; simpl; rewrite IHa2; reflexivity.
  - destruct a2;
    try (simpl; simpl in IHa2; rewrite IHa2; rewrite IHa1; reflexivity).
    + destruct n; simpl; rewrite IHa1; try rewrite sound_lemma; reflexivity.
  - destruct a1;
      try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    + destruct n; simpl; try rewrite IHa2; reflexivity.
Qed.

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

Require Import Coq.omega.Omega.

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n : nat), aevalR (ANum n) n
  | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
      aevalR e1 n1 -> aevalR e2 n2 -> aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
      aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
      aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMult e1 e2) (n1 * n2).

Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.


Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  split.
  - intros H.
    induction H; subst; reflexivity.
  - generalize dependent n.
    induction a; simpl; intros; subst; constructor; try  apply IHa1; try apply IHa2; reflexivity.
Qed.

Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : bevalR BTrue true
  | E_BFalse : bevalR BFalse false
  | E_BEq : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> bevalR (BEq a1 a2) (beq_nat n1 n2)
  | E_BLe : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> bevalR (BLe a1 a2) (leb n1 n2)
  | E_BNot : forall (e : bexp) (b : bool),
      bevalR e b -> bevalR (BNot e) (negb b)
  | E_BAnd : forall (e1 e2 : bexp) (b1 b2 : bool),
      (bevalR e1 b1) -> (bevalR e2 b2) -> bevalR (BAnd e1 e2) (andb b1 b2).

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  split.
  - intros H.
    induction H; simpl; try apply aeval_iff_aevalR in H; try apply aeval_iff_aevalR in H0; subst; try reflexivity.
  - generalize dependent bv.
    induction b; simpl; intros; subst; constructor; 
    try apply aeval_iff_aevalR; 
    try apply IHb; 
    try apply IHb1; try apply IHb2; 
    reflexivity.
Qed.

End AExp.

Module aevalR_division.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp. (* <--- new *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n : nat), aevalR (ANum n) n
  | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
      aevalR e1 n1 -> aevalR e2 n2 -> aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
      aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
      aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMult e1 e2) (n1 * n2)
  | E_ADiv : forall (e1 e2 : aexp) (n1 n2 : nat),
      aevalR e1 n1 -> aevalR e2 n2 -> n2 > 0 -> aevalR (ADiv e1 e2) (n1 / n2).

(* Relation is more powerful than function definition as how to handle 0 in our `aeval` Fixpoint in this case? *)
End aevalR_division.

Module aevalR_extended.

(* Suppose, instead, that we want to extend the arithmetic operations by a nondeterministic number generator any that, 
   when evaluated, may yield any number. *)

Inductive aexp : Type :=
  | AAny : aexp (* <--- NEW *)
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall (n:nat),
      aevalR AAny n (* <--- new *)
  | E_ANum : forall (n : nat), aevalR (ANum n) n
  | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
      aevalR e1 n1 -> aevalR e2 n2 -> aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
      aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
      aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMult e1 e2) (n1 * n2).

(* Similarlly we can't use function as the evaluation is not desterministic , but using relation (indproposistion) could acheive this *)
End aevalR_extended.


Definition state := total_map nat.

Definition empty_state : state :=
  t_empty 0.

Print id.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Definition X : id := Id 1.
Definition Y : id := Id 2.
Definition Z : id := Id 3.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (st : state) (a: aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Example aexpl :
  aeval (t_update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2))) = 13.
Proof.
  reflexivity.
Qed.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).


(* BNF:
 c ::= SKIP | x ::= a | c ;; c | IFB b THEN c ELSE c FI 
         | WHILE b DO c END
*)

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId Z) (ANum 1).

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
  | SKIP => st
  | x ::= a1 =>
    t_update st x (aeval st a1)
  | c1 ;; c2 =>
      let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
  | IFB b THEN c1 ELSE c2 FI =>
      if (beval st b)
        then ceval_fun_no_while st c1
        else ceval_fun_no_while st c2
  | WHILE b DO c END =>
      st (* bogus *)
end.
(* Coq don't accept non-terminating fuction because of Coq is a consistent logic *)

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).
Inductive ceval : com -> state -> state -> Prop :=
  | E_SKip : forall st,
     SKIP / st \\ st
  | E_Ass : forall st a1 n x,
     aeval st a1 = n ->
     (x ::= a1 ) / st \\ (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
     c1 / st \\ st' ->
     c2 / st' \\ st'' ->
    (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
    beval st b = true ->
    c1 / st \\ st' ->
    (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
    beval st b = false ->
    c2 / st \\ st' ->
    (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall b st c,
    beval st b = false ->
    (WHILE b DO c END) / st \\ st
  | E_WhileLoop : forall st st' st'' b c,
    beval st b = true ->
    c / st \\ st' ->
    (WHILE b DO c END) / st' \\ st'' ->
    (WHILE b DO c END) / st \\ st''

where "c1 '/' st '\\' st'" := (ceval c1 st st').

Example ceval_example1:
  (X ::= ANum 2;;
   IFB BLe (AId X) (ANum 1)
    THEN Y ::= ANum 3
    ELSE Z ::= ANum 4
   FI)
  / empty_state
  \\ (t_update (t_update empty_state X 2) Z 4).
Proof.
  apply E_Seq with (t_update empty_state X 2).
  - apply E_Ass. reflexivity.
  - apply E_IfFalse.
    + reflexivity.
    + apply E_Ass. reflexivity.
Qed.

Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state \\
    (t_update (t_update (t_update empty_state X 0) Y 1) Z 2).
Proof.
   apply E_Seq with (t_update empty_state X 0).
   - apply E_Ass. reflexivity.
   - apply E_Seq with (t_update (t_update empty_state X 0) Y 1).
    + apply E_Ass. reflexivity.
    + apply E_Ass. reflexivity.
Qed.

Definition pup_to_n : com :=
  Y ::= ANum 0 ;;
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Y ::= APlus (AId X) (AId Y) ;;
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem pup_to_2_ceval :
  pup_to_n / (t_update empty_state X 2) \\
    t_update (t_update (t_update (t_update (t_update (t_update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  apply E_Seq with (t_update (t_update empty_state
      X 2) Y 0).
  - apply E_Ass. reflexivity.
  - apply E_WhileLoop with (t_update (t_update(t_update (t_update empty_state
      X 2) Y 0) Y 2) X 1).
    + reflexivity.
    + apply E_Seq with  (t_update (t_update (t_update empty_state X 2) Y 0) Y 2); apply E_Ass; reflexivity.
    + apply E_WhileLoop with (t_update (t_update (t_update (t_update (t_update (t_update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0).
      * reflexivity.
      * apply E_Seq with (t_update (t_update (t_update (t_update (t_update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) ; apply E_Ass; reflexivity.
      * apply E_WhileEnd. reflexivity.
Qed.


Theorem ceval_deterministic: forall c st st1 st2,
     c / st \\ st1 ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;
           intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b1 evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b1 evaluates to false (contradiction) *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1 evaluates to true (contradiction) *)
    rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1 evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileEnd, b1 evaluates to false *)
    reflexivity.
  - (* E_WhileEnd, b1 evaluates to true (contradiction) *)
    rewrite H in H2. inversion H2.
  - (* E_WhileLoop, b1 evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* E_WhileLoop, b1 evaluates to true *)
      assert (st' = st'0) as EQ1.
      { (* Proof of assertion *) apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption. Qed.

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st \\ st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. clear Heval. simpl. apply t_update_eq.
Qed.

Theorem XtimesYinZ_spec : forall st n m st',
  st X = n ->
  st Y = m ->
  XtimesYinZ / st \\ st' ->
  st' Z = n * m.
Proof.
  intros st n m st' HX HY Heval.
  inversion Heval. subst. clear Heval. simpl. apply t_update_eq.
Qed.

Theorem loop_never_stops : forall st st',
  ~(loop / st \\ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef
           eqn:Heqloopdef.
  induction contra; try (inversion Heqloopdef).
  - subst. inversion H.
  - subst. apply IHcontra2. assumption.
Qed. 


Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END =>
      false
  end.

Inductive no_whilesR: com -> Prop :=
  | NW_Skip : no_whilesR SKIP
  | NW_CAss : forall i a, no_whilesR (i ::= a)
  | NW_CSeq : forall c1 c2, 
        no_whilesR c1 -> no_whilesR c2 -> no_whilesR (c1 ;; c2)
  | NW_CIf  : forall b c1 c2, 
        no_whilesR c1 -> no_whilesR c2 -> no_whilesR (IFB b THEN c1 ELSE c2 FI).

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split.
  - induction c; intros H.
    + constructor.
    + constructor.
    + apply andb_true_iff in H. inversion H. apply NW_CSeq; try apply IHc1; try apply IHc2; assumption.
    + apply andb_true_iff in H. inversion H. apply NW_CIf; try apply IHc1; try apply IHc2; assumption.
    + inversion H.
  - induction c; intros H.
    + constructor.
    + constructor.
    + inversion H. apply andb_true_iff. split; try apply IHc1; try apply IHc2; assumption.
    + inversion H. apply andb_true_iff. split; try apply IHc1; try apply IHc2; assumption.
    + inversion H.
Qed.
