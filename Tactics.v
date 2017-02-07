Add LoadPath "/Users/chenshen/src/sf/".
Require Export Poly.

(* apply Tactic *)

Theorem silly1 : forall (n m o p : nat),
  n = m ->
  [n; o] = [n; p] ->
  [n; o] = [m; p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1. apply eq2. Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (forall (q r: nat), q = r -> [q;o] = [r; p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.


Theorem silly_ex:
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true ->
  oddb 4 = true.
Proof.
  intros eq1 eq2. apply eq1. apply eq2. Qed.

Theorem silly3: forall (n : nat),
  true = beq_nat n 5 ->
  beq_nat (S (S n)) 7 = true.
Proof.
  intros n eq1.
  symmetry. apply eq1. Qed.

SearchAbout rev.

Theorem rev_exercise1 : forall(l l': list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l' eq1. rewrite eq1. symmetry. apply rev_involutive. Qed.


Example trans_eq_example : forall(a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.  
intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example1 : forall(a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]). apply eq1. apply eq2. Qed. 

Example trans_eq_excersise: forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with m. apply eq2. apply eq1. Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H. inversion H. reflexivity. Qed.

Theorem inversion_ex1 : forall (n m o: nat),
  [n;m] = [o;o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem f_equal : forall(A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros n. destruct n as [|n'].
  - intros H. reflexivity.
  - simpl. intros H. inversion H. Qed.

Example inversion_ex6 : forall (X: Type) (x y z:X) (l j : list X),
  x::y::l = [] ->
  y :: l = z :: j ->
  x = z.
Proof.
  intros X x y z l j H1 H2. 
  inversion H1. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b ->
     beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

SearchAbout plus.

Lemma eq_remove_S : forall n m,
  n = m -> S n = S m.
Proof. intros n m eq. rewrite -> eq. reflexivity. Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [|n'].
   - intros m H. destruct m as [|m'].
    + reflexivity.
    + simpl in H. inversion H.
   - intros m H. destruct m as [|m'].
    + simpl in H. inversion H.
    + simpl in H. 
      rewrite <- plus_n_Sm in H. symmetry in H. 
      rewrite <- plus_n_Sm in H. inversion H. symmetry in H1. 
      apply IHn' in H1. rewrite -> H1. reflexivity. Qed.


Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'].
    + (* m = O *) reflexivity.
    + (* m = S m' *) inversion eq.
  - (* n = S n' *) intros eq. destruct m as [| m'].
    + (* m = O *) inversion eq.
    + (* m = S m' *) apply f_equal.
Abort.

(* 
Trying to carry out this proof by induction on n when m is already in the context doesn't work 
because we are then trying to prove a relation involving every n but just a single m.

What you should take away from all this is that we need to be careful about using induction to try to prove something too specific: 
If we're proving a property of n and m by induction on n, we may need to leave m generic.
*)

Theorem beq_nat_true : forall n m,
  beq_nat n m = true -> n = m.
Proof.
  intros n. induction n as [|n'].
  - intros [|m'].
    + reflexivity.
    + intros H. inversion H.
  - intros m H. destruct m as [|m'].
    + inversion H.
    + simpl in H. apply f_equal. apply IHn' in H. apply H. Qed.

(*
Theorem: For any nats n and m, if beq_nat n m = true, then n = m.
Proof: By induction on n. 
  - First support n = 0. we must show
     if beq_nat 0 m = true, then 0 = m.
    + If m is O, beq_nat 0 m = true, and m = 0.
    + If m is S m'. By definitnion beq_nat 0 m is always be false.
  - Next suppose n = S n' where for any nats m whe have if beq_nat n' m = true, then n' = m. (H0)
    we must show for any nats m we have if beq_nat Sn' m = true, then Sn'= m. (H1)
    + If m is O. By definition beq_nat Sn' O = false.
    + If m is Sm'. By simply H1 we got beq_nat n' m' = true. By applying H0 to H1 we have n' = m'. 
*)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *) apply f_equal.
        (* Stuck again here, just like before. *)
Abort.

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. inversion eq. reflexivity. Qed.

Theorem beq_id_true : forall x y,
  beq_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply beq_nat_true. apply H. }
  rewrite H'. reflexivity.
Qed.

Check beq_id.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [|m l' IHl'].
  - intros n H. simpl in H. rewrite <- H. reflexivity.
  - intros [|n'] H.
    + inversion H.
    + simpl. simpl in H. inversion H. rewrite H1. apply IHl' in H1. apply H1. Qed.

Theorem app_length_cons : forall(X : Type) (l1 l2 : list X)
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  intros X l1. induction l1 as [|y l1' IHl1'].
  - intros l2 x n H. simpl in H. simpl. apply H.
  - intros l2 x n H. destruct n as [|n'].
    + inversion H.
    + simpl in H. inversion H. rewrite -> H1. apply IHl1' in H1. simpl. rewrite <- H1. reflexivity. Qed.

Theorem length_swap : forall (X: Type) (l1 l2 : list X),
  length(l1 ++ l2) = length (l2 ++ l1).
Proof.
  intros X l1.
  induction l1 as [|n l1' IHl1'].
  - intros l2. induction l2 as [|m l2' IHl2'].
    + reflexivity.
    + simpl in IHl2'. simpl. rewrite -> IHl2'. reflexivity.
  - intros l2. induction l2 as [|m l2' IHl2'].
    + simpl. rewrite -> IHl1'. reflexivity.
    + simpl. rewrite <- IHl2'. rewrite -> IHl1'. simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  intros X n l.
  generalize dependent n.
  induction l as [|m l' IHl'].
  - intros n H. simpl in H. rewrite <- H. reflexivity.
  - intros n H. destruct n as [|n'].
   + inversion H.
   + simpl in H. inversion H. rewrite -> H1. apply IHl' in H1. simpl.
     rewrite <- plus_n_Sm. rewrite -> length_swap. rewrite <- H1. reflexivity. Qed.

Check Prop.

Theorem double_induction: forall (P : nat -> nat -> Prop),
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n ->P (S m) (S n)) ->
  forall m n, P m n.
Proof.
  intros p H0 H1 H2 H3 m.
  induction m as [| m'].
  - induction n as [|n'].
    + apply H0.
    + apply H2 in IHn'. apply IHn'.
  - induction n as [|n'].
    + apply H1 in IHm'. apply IHm'.
    + apply H3. apply IHm'. Qed.

Definition square n := n * n.
Lemma suqare_mult : forall n m, square (n * m) = square n * square m.
Proof. intros n m.
  simpl. unfold square. rewrite mult_assoc. 
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
  Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    - (* beq_nat n 3 = true *) reflexivity.
    - (* beq_nat n 3 = false *) destruct (beq_nat n 5).
      + (* beq_nat n 5 = true *) reflexivity.
      + (* beq_nat n 5 = false *) reflexivity. Qed.


Theorem combin_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [|n l' IHl'].
  - intros l1 l2 H. inversion H. reflexivity.
  - intros l1 l2 H. destruct l1.
    + destruct n. simpl in H. destruct (split l'). inversion H.
    + simpl in H. destruct n. destruct (split l'). destruct l2.
      * inversion H.
      * inversion H. simpl. apply f_equal. apply IHl'. rewrite  H2,H4. reflexivity. Qed.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* stuck... *)
Abort.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
   - (* e3 = true *) apply beq_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
     (* When we come to the second equality test in the body
        of the function we are reasoning about, we can use
        eqn: again in the same way, allow us to finish the
        proof. *)
      destruct (beq_nat n 5) eqn:Heqe5.
        + (* e5 = true *)
          apply beq_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) inversion eq. Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. destruct b eqn: Heq1.
  - destruct (f true) eqn: Heq2.
    + rewrite -> Heq2. rewrite -> Heq2. reflexivity.
    + destruct (f false) eqn: Heq3.
      * apply Heq2.
      * apply Heq3.
  - destruct (f false) eqn: Heq2.
    + destruct (f true) eqn : Heq3.
      * apply Heq3.
      * apply Heq2.
    + rewrite -> Heq2. rewrite -> Heq2. reflexivity.
Qed.

SearchAbout beq_nat_true.

Theorem beq_nat_sym : forall(n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n as [|n'].
  - intros m. destruct m.
    + reflexivity.
    + reflexivity.
  - intros m. destruct m.
    + reflexivity.
    + simpl. apply IHn'.
Qed.

Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  intros n m p eq1 eq2.
  apply beq_nat_true in eq1. apply beq_nat_true in eq2. rewrite eq1. rewrite eq2. 
  assert (eq3: forall r, beq_nat r r = true).
  {
      intros r. induction r as [|r' IHr'].
      - reflexivity.
      - simpl. apply IHr'.
  } 
  apply eq3.
Qed.

Definition split_combine_statement : Prop :=
  forall X Y (l : list (X * Y)) l1 l2,
  combine l1 l2 = l ->
  length l1 = length l ->
  length l2 = length l ->
  split l = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l.
  induction l as [|n l' IHl'].
  - intros l1 l2 eq1 eq2 eq3. inversion eq2. destruct l1 as [|n l1'].
    + inversion eq3. destruct l2 as [|m l2'].
      * reflexivity.
      * inversion H1.
    + inversion H0.
  - intros l1 l2 eq1 eq2 eq3. destruct l1 as [|m l1'].
    + inversion eq2.
    + destruct l2 as [|o l2'].
      * inversion eq3.
      * inversion eq2. inversion eq3. simpl in eq1. inversion eq1. 
        simpl. rewrite -> H3. destruct (split l').
        assert (H4: (l, l0) = (l1', l2') -> (m :: l, o :: l0) = (m :: l1', o :: l2')).
        { intros H5. inversion H5. rewrite <- H4. rewrite <- H6. reflexivity. }
        apply H4. apply IHl'. apply H3. apply H0. apply H1.
Qed.


