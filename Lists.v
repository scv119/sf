Add LoadPath "/Users/chenshen/src/sf/".

Require Export Induction.
Module NatList.

Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
    | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
    | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x , y) => (y, x)
  end.


Theorem subjective_pairing' : forall n m : nat,
  (n, m) = (fst (n, m), snd (n, m)).
Proof. reflexivity. Qed.

Theorem snd_fst_is_swap : forall p : natprod,
  (snd p, fst p) = swap_pair p.
Proof.
  intros [n m]. reflexivity. Qed.

Theorem fst_swap_is_snd : forall p : natprod,
  fst (swap_pair p) = snd p.
Proof.
  intros [n m]. reflexivity. Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1  with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with 
  | nil => nil
  | h :: t => t
  end.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | O :: t => (nonzeros t)
  | m :: t => m :: (nonzeros t)
  end.

Example test_nonzeros: 
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l: natlist) : natlist :=
  match l with
  | nil => nil
  | n :: t => match oddb(n) with
              | true => n :: (oddmembers t)
              | false => oddmembers t
              end
  end.

Example test_oddmembers:
  oddmembers [0;1;2;3;0;0;2] = [1;3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  match l with
  | nil => O
  | n :: t => match oddb(n) with
              | true => S (countoddmembers t)
              | false => countoddmembers t
              end
  end.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist:=
  match l1,l2 with
  | nil,_ => l2
  | _,nil => l1
  | s :: t, p :: q => [s;p] ++ (alternate t q)
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) :nat :=
  match s with
  | nil => 0
  | n :: m => match beq_nat n v with
              | true => 1 + (count v m)
              | false => count v m
              end
  end.

Example test_couint1: count 1 [1;2;3;4;1;1] = 3.
Proof. reflexivity. Qed.

Example test_count2 : count 6 [1;2;3;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag:= v :: s.


Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Fixpoint member (v:nat) (s:bag) : bool :=
  match s with
   | nil => false
   | m :: n => match beq_nat m v with
                | true => true
                | false => member v n
               end
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v: nat) (s: bag) : bag :=
  match s with
  | nil => nil
  | n :: m  => match beq_nat n v with
               | true => m
               | false => n :: remove_one v m
               end
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v: nat) (s: bag) :bag :=
  match s with
  | nil => nil
  | n :: m  => match beq_nat n v with
               | true => remove_all v m
               | false => n :: (remove_all v m)
               end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Compute (remove_all 5 [2;1;5;4;5;1;4;5;1;4]).

Example test_remove_all4: remove_all 5 [2;1;5;4;5;1;4;5;1;4] = [2;1;4;1;4;1;4].
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil => true
  | n :: m => match member n s2 with
              | true => subset m (remove_one n s2)
              | false => false
              end
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l : natlist,
  pred (length l) = length (tl l).
Proof.
  intros [|n l'].
  - reflexivity.
  - reflexivity. Qed.


Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [|n l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
  Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1 : rev[1;2;3] = [3;2;1].
Proof. reflexivity. Qed.

Theorem ref_legnth_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l1. induction l1 as [|n l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHl1'.
Abort.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [|n l1 IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHl1'. reflexivity. Qed.

Theorem rev_legnth : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l1. induction l1 as [|n l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite -> app_length. rewrite <- IHl1', plus_comm. reflexivity. Qed.

SearchAbout rev.

Theorem app_nil_r : forall l :natlist,
  l ++ [] = l.
Proof. 
  intros l. induction l as [|n l1 IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem rev_swap : forall l1 l2 : natlist,
  rev(l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2. induction l1 as [|n l1' IHl1'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1', app_assoc. reflexivity. Qed.


Theorem rev_involutive: forall l : natlist,
  rev(rev l) = l.
Proof.
  intros l. induction l as [|n l1 IHl1'].
  - reflexivity.
  - simpl. rewrite -> rev_swap. rewrite -> IHl1'. reflexivity. Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. simpl. rewrite -> app_assoc. rewrite -> app_assoc. reflexivity. Qed.

Theorem nonzero_app : forall l1  l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [|n l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1'. destruct n.
    + reflexivity.
    + reflexivity.
  Qed.

Fixpoint beq_natlist (l1 l2: natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | s :: t, n::m => match beq_nat s n with
                   | true => beq_natlist t m
                   | false => false
                   end
  | _, _ => false
  end.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros l. induction l as [|n l1 IHl1'].
  - reflexivity.
  - simpl. rewrite <- IHl1'.
    assert (H: beq_nat n n = true).
    { induction n as [|n' IHn'].
      + reflexivity.
      + simpl. rewrite -> IHn'. reflexivity.
    }
    rewrite -> H. reflexivity. Qed.

Theorem count_member_nonzero : forall s : bag,
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  intros l. simpl. reflexivity. Qed.

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_decreases_count: forall(s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s. induction s as [|n s1 IHs1].
  - reflexivity.
  - destruct n.
    + simpl. rewrite -> ble_n_Sn. reflexivity.
    + simpl. rewrite -> IHs1. reflexivity. Qed.

Theorem rev_injective: forall l1 l2 : natlist,
  rev l1 = rev l2 -> l1 = l2.
Proof. 
  intros l1 l2 H. rewrite <- rev_involutive. rewrite <- H.  rewrite -> rev_involutive. reflexivity. Qed.


Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
              | true => Some a
              | false => nth_error l' (pred n)
              end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.


Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with 
  | nil => None
  | s :: t => Some(s)
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default. destruct l as [| n l'].
  - simpl. reflexivity.
  - reflexivity. Qed.

End NatList.