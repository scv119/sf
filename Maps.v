Add LoadPath "/Users/chenshen/src/sf/".

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id id1 id2 :=
  match id1, id2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof. intros id. destruct id. simpl. apply beq_nat_refl. Qed.

Theorem beq_id_true_iff : forall id1 id2 : id,
  beq_id id1 id2 = true <-> id1 = id2.
Proof.
  intros [n1] [n2].
  unfold beq_id.
  rewrite beq_nat_true_iff.
  split.
  - intros H. rewrite H. reflexivity.
  - intros H. inversion H. rewrite <- H1. reflexivity.
Qed.

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem false_beq_id : forall x y : id,
  x <> y -> beq_id x y = false.
Proof.
  intros x y. rewrite beq_id_false_iff. intros H. apply H. Qed.

Definition total_map (A:Type) := id -> A.

Check total_map.
Check total_map nat.

Definition t_empty {A:Type} (v:A) : total_map A :=
  (fun _ => v).

Definition t_update {A:Type} (m :total_map A) (x: id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) (Id 1) false) (Id 3) true.

Example update_example1 : examplemap (Id 0) = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap (Id 1) = false.
Proof. reflexivity. Qed.

Example update_example3 : examplemap (Id 3) = true.
Proof. reflexivity. Qed.

Lemma t_apply_empty : forall A x v, @t_empty A v x = v.
Proof.
  intros A x v. unfold t_empty. reflexivity.
Qed.

Lemma t_update_eq : forall A (m : total_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros A m x v. unfold t_update. rewrite <- beq_id_refl. reflexivity.
Qed.

Lemma t_update_neq : forall (X:Type) v x1 x2 (m : total_map X),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof.
  intros X v x1 x2 m H. unfold t_update. apply false_beq_id in H. rewrite H. reflexivity.
Qed.

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
  t_update (t_update m x v1 ) x v2
  = t_update m x v2.
Proof.
  intros A m v1 v2 x. apply functional_extensionality.
  intros x0. unfold t_update. destruct (beq_id x x0).
  - reflexivity.
  - reflexivity.
Qed.

Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
Proof.
  intros x y. destruct (beq_id x y) eqn: Heq.
  - apply ReflectT. apply beq_id_true_iff. apply Heq.
  - apply ReflectF. apply beq_id_false_iff. apply Heq.
Qed.

Theorem t_update_same: forall X x (m: total_map X),
  t_update m x (m x) = m.
Proof.
  intros X x m. apply functional_extensionality.
  intros x0. destruct (beq_idP x0 x) as [H | H].
  - unfold t_update. rewrite H. rewrite <- beq_id_refl. reflexivity.
  - unfold t_update. assert (H1: x <> x0). { intros H1. apply H.  rewrite H1. reflexivity. } apply beq_id_false_iff in H1. rewrite H1. reflexivity.
Qed.

Lemma t_update_permute_lemma : forall (x y:id),
  x <> y -> y <> x.
Proof.
  intros x y H H1. apply H. symmetry. apply H1.
Qed.

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2 (m: total_map X),
  x2 <> x1 -> (t_update (t_update m x2 v2) x1 v1) = (t_update (t_update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m H1. apply functional_extensionality.
  intros x0. destruct (beq_idP x0 x1) as [H | H].
  - unfold t_update.
    assert (H2: beq_id x1 x0 = true). { apply beq_id_true_iff. rewrite H. reflexivity. }
    assert (H3: beq_id x2 x0 = false). { apply beq_id_false_iff. rewrite <- H in H1. apply H1. }
    rewrite H2. rewrite H3. reflexivity.
  - destruct (beq_idP x0 x2) as [H3 | H3].
    * unfold t_update.
      assert (H2: beq_id x2 x0 = true). { apply beq_id_true_iff. rewrite H3. reflexivity. }
      assert (H4: beq_id x1 x0 = false). { apply beq_id_false_iff. intros H4. apply H. rewrite H4. reflexivity. }
      rewrite H2. rewrite H4. reflexivity.
    * unfold t_update.
      apply t_update_permute_lemma in H. apply t_update_permute_lemma in H3.
      apply beq_id_false_iff in H. apply beq_id_false_iff in H3.
      rewrite H. rewrite H3. reflexivity.
Qed.

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Definition update {A:Type} (m: partial_map A) (x:id) (v:A) :=
  t_update m x (Some v).

(* Copy Pasta *)
Lemma apply_empty : forall A x, @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  update m x v = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
    (update (update m x2 v2) x1 v1)
  = (update (update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.