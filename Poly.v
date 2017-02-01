Add LoadPath "/Users/chenshen/src/sf/".
Require Export Lists.

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check nil.
Check cons.

Check (cons nat 2 ( cons nat 1 (nil nat))).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Module MumbleGrumble.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(* Check d (b a 5). *)
Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
(* Check e bool (b c 0). *)
Check c.
Check d bool c.

End MumbleGrumble.

(* Type Inference *)
Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(* Type Arugment Synthesis *)

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* Implicit Arguments  *)
Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list123'' := cons 1 (cons 2( cons 3 nil)). 

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

Fixpoint app {X:Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l: list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Fail Definition mynil := nil.

Definition mynil : list nat := nil.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem app_nil_r : forall X : Type, forall l : list X,
  l ++ [] = l.
Proof.
  intros X l. induction l as [|x l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem app_assoc: forall A (l m n : list A),
  l ++ m ++ n = (l ++ m ) ++ n.
Proof.
  intros A l m n. induction l as [|a l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem app_length : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2. induction l1 as [|x l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity. Qed.

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.
Notation "( x , y )" := (pair x y). (* A value *)
Notation "X * Y":= (prod X Y) : type_scope. (* A type *)

Definition fst {X Y : Type} (p : prod X Y ) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x ,y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Check @nil.
(* Forall X: Type Forall Y: Type, list X -> list Y -> list X*Y *)
Check @combine.

(* [(1, false);(2, false)] *)
Compute (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y : Type} (l: list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: l' => match split l' with 
                    | (lx, ly) => (x::lx, y::ly)
                    end
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Inductive option (X : Type) : Type :=
  | Some: X -> option X
  | None: option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n 0 then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.


Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | x :: _ => Some x
  end.

Check @hd_error.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X : Type} (f : X -> X ) (n : X) : X :=
  f (f (f n)).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Fixpoint filter {X : Type} (test: X -> bool) (l : list X) : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t) else filter test t
  end.


Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_annon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (leb 8 n)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition compose' {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Definition partition {X: Type} (test : X -> bool) (l : list X) : list X * list X :=
  (filter test l, filter (compose' negb test) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.