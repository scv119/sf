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


Theorem rev_swap : forall (X : Type) (l1 l2 : list X),
  rev(l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros X l1 l2. induction l1 as [|n l1' IHl1'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1', app_assoc. reflexivity. Qed.


Theorem rev_involutive: forall (X : Type) (l : list X),
  rev(rev l) = l.
Proof.
  intros X l. induction l as [|n l1 IHl1'].
  - reflexivity.
  - simpl. rewrite -> rev_swap. rewrite -> IHl1'. reflexivity. Qed.

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

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Theorem map_assoc : forall (X Y: Type) (f : X -> Y) (a b : list X),
  map f (a ++ b) = map f a ++ map f b.
Proof.
  intros X Y f a b. induction a as [|n c IHc].
  - reflexivity.
  - simpl. rewrite -> IHc. reflexivity. Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f ( rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl', map_assoc. reflexivity. Qed.

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X) : (list Y) :=
  match l with 
  | [] => []
  | s :: t => f s ++ flat_map f t
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Fixpoint fold {X Y:Type} (f: X -> Y -> Y) (l:list X) (b:Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition constfun {X : Type} (x : X) : nat -> X :=
  fun (k : nat) => x.

Module Exercises.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall (X :Type) (l : list X),
  fold_length l = length l.
Proof. intros X l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'. reflexivity. Qed.

Definition fold_map {X Y:Type} (f : X -> Y) (l: list X) : list Y :=
  fold (fun s t => (f s) :: t) l [].

Theorem map_fold_correct : forall (X Y: Type) (f : X -> Y) (l : list X),
  map f l = fold_map f l.
Proof. intros X Y f l. induction l as [|n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity. Qed.

Definition prod_curry {X Y Z: Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z: Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  match p with
  | (x, y) => f x y
  end.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y. reflexivity. Qed.


Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.  destruct p as [x y].
  - reflexivity. Qed.

Theorem nth_error_length :  forall (X : Type) (l : list X),
  nth_error l (length l) = None.
Proof. intros X l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem nth_error_length_none : forall (X : Type) (n : nat) (l : list X),
  length l = n -> nth_error l n = None.
Proof.
  intros X n l H. rewrite <- H. rewrite -> nth_error_length. reflexivity. Qed.

Module Church.
Definition nat := forall (X : Type), (X -> X) -> X -> X.
Definition one : nat :=
  fun (X : Type) (f: X -> X) (x : X) => f x.
Definition two : nat :=
  fun (X : Type) (f: X -> X) (x : X) => f (f x).
Definition zero : nat :=
  fun (X : Type) (f: X -> X) (x : X) => x.
Definition three : nat := @doit3times.


Definition succ (n : nat) : nat :=
  fun (X : Type) (f: X -> X) (x : X) => f (n X f x).

Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.

Example succ_2 : succ one = two.
Proof. reflexivity. Qed.

Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

Definition plus (n m : nat) : nat :=
  fun (X : Type) (f: X -> X) (x : X) => m X f (n X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.

Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

Definition mult (n m : nat) : nat :=
  fun (X : Type) (f: X -> X) (x : X) => (n X (m X f)) x.

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.

Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

(* By observate that 

(multi m m) f x = m (m f) x

we could see 

exp n m f = n (n ( n ... f))

So we should apply m to n, the only problem is type.

Given n has type X : (X -> X) -> X -> X
for m we have   Y : (Y -> Y) -> Y -> Y, 
wehere Y -> Y  == (X -> X) -> (X -> X)
we could see Y = ( X -> X).
*)

Definition exp (n m : nat) : nat := 
  fun (X : Type) (f: X -> X) (x : X) => (m _ (n X)) f x.

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

Example exp_3 : exp three zero = one.
Proof. reflexivity. Qed.

End Church.

End Exercises.
