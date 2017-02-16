Add LoadPath "/Users/chenshen/src/sf/".
Require Export Logic.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).


Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : forall n, wrong_ev n -> wrong_ev (S (S n)).
(* ===> Error: A parameter of an inductive type n is not
        allowed to be used as a bound variable in the type
        of its constructor. *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn'.
Qed.


Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros [ | [ | n' ] ].
  - simpl. intros _. apply ev_0.
  - simpl. intros _. apply ev_0.
  - simpl.
Abort.


Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion  E as [|n' E'].
  - simpl. apply ev_0.
  - simpl. apply E'.
Qed.

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct  E as [|n' E'].
  - simpl. apply ev_0.
  - simpl. apply E'.
Qed.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  destruct E as [|n' E'].
Abort.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [|n' E'].
  apply E'.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H. inversion H. inversion H1. inversion H3.
Qed.

Lemma ev_even : forall n, 
  ev n -> exists k, n = double k.
Proof.
  intros n E. inversion E as [| n' E'].
  - exists 0. reflexivity.
Abort.

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E. 
  induction E as [|n' E' IH].
  - exists 0. reflexivity.
  - destruct IH as [k' IH'].
    exists (S k'). rewrite IH'. reflexivity.
Qed.

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.


Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m E1 E2.
  induction E1 as [|n' E1' IHE1'].
  - simpl. apply E2.
  - rewrite plus_comm. SearchAbout plus. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. apply ev_SS. rewrite plus_comm. apply IHE1'.
Qed.

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
 intros n. split.
 - intros E. induction E.
  + apply ev_0.
  + apply (ev_SS 0 ev_0).
  + apply ev_sum. apply IHE1. apply IHE2.
 - intros E. induction E.
  + apply ev'_0.
  + assert (H: ev' (2 + n)). 
    { apply ev'_sum. apply ev'_2.  apply IHE. }
    unfold plus in H. apply H.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m E1 E2. induction E2 as [|n' E2' IH].
  - simpl in E1. apply E1.
  - rewrite plus_comm in E1. rewrite <- plus_n_Sm in E1. rewrite <- plus_n_Sm in E1. inversion E1. apply IH.  rewrite plus_comm. apply H0.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p E1 E2. apply ev_ev__ev with (n:=(n + n)).
  - rewrite plus_assoc. rewrite plus_comm. SearchAbout plus. rewrite <- plus_assoc. rewrite plus_assoc.
    apply ev_sum with (n:=(p + n)). rewrite plus_comm. apply E2. apply E1.
  - apply ev_even_iff. exists n. SearchAbout plus. Admitted.

Module LeModule.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply (le_S 3 5 (le_S 3 4 (le_S 3 3 (le_n 3)))).
Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H. inversion H. inversion H2.
Qed.

End LeModule.

Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n: nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n: nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation : nat -> nat -> Prop :=
  tr : forall n m, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop :=
  er : forall n m,  0 = 1 -> empty_relation n m.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2. induction H2 as [|o' H3 H4].
  - apply H1.
  - apply le_S. apply H4.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n as [|n' H].
  - apply le_n.
  - apply le_S. apply H.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H. induction H as [|m' H' IH].
  - apply le_n.
  - apply le_S. apply IH.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  - apply le_n.
  - apply le_trans with (n:= S n). apply le_S. apply le_n. apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b. induction b as [|b' IH].
  - rewrite plus_comm. simpl. apply le_n.
  - SearchAbout plus. rewrite <- plus_n_Sm. apply le_S. apply IH.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
  intros n1 n2 m H. split.
  - apply le_trans with (n:= S (n1 + n2)).
    + apply n_le_m__Sn_le_Sm. apply le_plus_l.
    + apply H.
  - apply le_trans with (n:= S (n1 + n2)).
    + apply n_le_m__Sn_le_Sm. rewrite plus_comm. apply le_plus_l.
    + apply H.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros n m H. apply le_S. apply H.
Qed.

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  intros n m H.
  generalize dependent m.  
  induction n as [|n' IH].
  - intros m. intros H. apply O_le_n.
  - intros m. intros H. destruct m as [|m'].
    + inversion H.
    + simpl in H. apply n_le_m__Sn_le_Sm. apply IH. apply H.
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m' IH].
  - intros n H. inversion H. reflexivity.
  - intros n H. destruct n as [|n'].
    + reflexivity.
    + simpl. apply IH. apply Sn_le_Sm__n_le_m. apply H.
Qed.

Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  intros n m o H1 H2. apply leb_correct. apply leb_complete in H1. apply leb_complete in H2.
  apply le_trans with (n:=m). apply H1. apply H2.
Qed.

Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  split. apply leb_complete. apply leb_correct.
Qed.


Module R.

Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 : forall m n o, R m n o -> R (S m) n (S o)
  | c3 : forall m n o, R m n o -> R m (S n) (S o)
  | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
  | c5 : forall m n o, R m n o -> R n m o.

(* 
1. R 1 1 2 Provable, R 2 2 6 Not.
2. nope, c1 c2 3 -> c5.
3. nope  same reason
*)

Definition fR (a:nat) (b: nat) : nat :=
  a + b.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  intros m n o. unfold fR. split.
  - intros H. induction H.
    + reflexivity.
    + rewrite plus_comm. rewrite <- plus_n_Sm. rewrite plus_comm. rewrite IHR. reflexivity.
    + rewrite <- plus_n_Sm. rewrite IHR. reflexivity.
    +  rewrite <- plus_n_Sm in IHR. inversion IHR. reflexivity.
    +  rewrite plus_comm. apply IHR. 
  - generalize dependent m.
    generalize dependent n.
    induction o as [|o' H].
    + intros [|n'] [|m'] H.
      * apply c1.
      * inversion H.
      * inversion H.
      * inversion H.
    + intros n [|m'] H1.
      * simpl in H1. destruct n. 
        inversion H1.
        inversion H1. apply c3. apply H. reflexivity.
      * apply c2. apply H. rewrite plus_comm in H1. rewrite <- plus_n_Sm in H1. inversion H1.
        apply plus_comm.
Qed.

End R.

Inductive subseq : list nat -> list nat -> Prop :=
  | ss1 : subseq [] []
  | ss2 : forall n l1 l2, subseq l1 l2 -> subseq l1 (n::l2)
  | ss3 : forall n l1 l2, subseq l1 l2 -> subseq (n::l1) (n::l2).

Theorem subseq_refl : forall l, subseq l l.
Proof. 
  intros l. induction l as [|n' l' IH].
  - apply ss1.
  - apply ss3. apply IH.
Qed.

Lemma subseq_empty: forall l,
  subseq [] l.
Proof.
  Admitted.

Theorem subse_app : forall l1 l2 l3,
  subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 H. induction H.
  - induction l3 as [|n l3' IHl3'].
    + simpl. apply ss1.
    + simpl. apply ss2. simpl in IHl3'. apply IHl3'.
  - simpl. apply ss2. apply IHsubseq.
  - simpl. apply ss3. apply IHsubseq.
Qed.


Inductive reg_exp (T : Type) : Type :=
| EmptySet : reg_exp T
| EmptyStr : reg_exp T
| Char : T -> reg_exp T
| App : reg_exp T ->reg_exp T -> reg_exp T
| Union : reg_exp T -> reg_exp T -> reg_exp T
| Star : reg_exp T -> reg_exp T.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x, exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
      exp_match s1 re1 -> exp_match s2 re2 -> exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0 : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2] _).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.


Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H. inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [H|H].
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H. induction ss.
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
    + apply H. simpl. left. reflexivity.
    + apply IHss. intros s H1. apply H. simpl. right. apply H1.
Qed.

Lemma list_empty : forall T (s1 s2 : list T),
  s1 ++ s2 = [] -> s1 = [].
Admitted.

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros T s1 s2. split.
  - generalize dependent s1. induction s2 as [|n s2' IHs2'].
    + intros s1. simpl. intros H. inversion H. reflexivity.
    + intros s1 H. destruct s1 as [|m s1'].
      * simpl in H. inversion H. apply list_empty in H0. rewrite H0 in H3. inversion H3.
      * simpl in H. inversion H. inversion H3. simpl. apply f_equal. apply IHs2'. apply H4.
  - generalize dependent s1. induction s2 as [|n s2' IHs2'].
    + intros s1 H. rewrite H. simpl. apply MEmpty.
    + intros s1 H. rewrite H. simpl. apply (MApp [n]).
      * apply MChar.
      * apply IHs2'. reflexivity.
Qed.
