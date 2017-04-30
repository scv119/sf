Add LoadPath "/Users/chenshen/src/sf/".

Require Import Coq.Arith.Arith.
Require Import Maps.
Require Import Imp.
Require Import Smallstep.

Hint Constructors multi.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Definition value (t: tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold update.

Reserved Notation "t1 '=>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) => t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) => t2
  | ST_If : forall t1 t1' t2 t3,
      t1 => t1' ->
      (tif t1 t2 t3) => (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 => t1' ->
      (tsucc t1) => (tsucc t1')
  | ST_PredZero :
      (tpred tzero) => tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) => t1
  | ST_Pred : forall t1 t1',
      t1 => t1' ->
      (tpred t1) => (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) => ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) => tfalse
  | ST_Iszero : forall t1 t1',
      t1 => t1' ->
      (tiszero t1) => (tiszero t1')

where "t1 '=>' t2" := (step t1 t2).

Hint Constructors step.

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (tsucc ttrue). unfold stuck. unfold step_normal_form. split.
  - unfold not. intros H. inversion H. inversion H0. subst. inversion H2.
  - unfold not. intros. inversion H. inversion H0. inversion H0. inversion H2.
Qed.

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros. inversion H.
  - unfold step_normal_form. intros contra. inversion H0; subst; inversion contra; inversion H1.
  - unfold step_normal_form. induction H0. 
    + intros contra. inversion contra. inversion H0.
    + intros contra. inversion contra. inversion H1. subst. assert (value t) by auto. apply IHnvalue in H2 .
      eauto.
Qed.
    
Ltac inv H := inversion H; subst; clear H.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic. intros x. induction x; intros; inversion H; subst; clear H.
  - inversion H0; subst. reflexivity. inversion H4.
  - inversion H0; subst. reflexivity. inversion H4.
  - inversion H0; subst. inversion H5. inversion H5. assert (t1' = t1'0) by auto. subst. auto.
  - inversion H0; subst. assert (t1' = t1'0) by auto. subst. auto.
  - inversion H0; subst. reflexivity. inversion H0. inversion H1.
  - inversion H0; subst. reflexivity. assert (value (tsucc y1)) by auto. apply value_is_nf in H.
    unfold step_normal_form in H. exfalso. apply H. eauto.
  - inversion H0; subst. inversion H2. 
    assert (value (tsucc y2)) by auto. apply value_is_nf in H.
    unfold step_normal_form in H. exfalso. apply H. eauto. apply f_equal. auto.
  - inversion H0; subst. reflexivity. inversion H1.
  - inversion H0; subst. reflexivity. assert (value (tsucc t1)) by auto. apply value_is_nf in H.
    unfold step_normal_form in H. exfalso. apply H. eauto.
  - inversion H0; subst.
    + inversion H2.
    + assert (value (tsucc t1)) by auto. apply value_is_nf in H.
    unfold step_normal_form in H. exfalso. apply H. eauto.
    + apply f_equal. auto.
Qed.

Inductive ty : Type :=
  | TBool : ty
  | TNat : ty.

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |- ttrue \in TBool
  | T_False :
       |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in TBool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- tif t1 t2 t3 \in T
  | T_Zero :
       |- tzero \in TNat
  | T_Succ : forall t1,
       |- t1 \in TNat ->
       |- tsucc t1 \in TNat
  | T_Pred : forall t1,
       |- t1 \in TNat ->
       |- tpred t1 \in TNat
  | T_Iszero : forall t1,
       |- t1 \in TNat ->
       |- tiszero t1 \in TBool

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type.

Example has_type_1 :
  |- tif tfalse tzero (tsucc tzero) \in TNat.
Proof.
  apply T_If.
    - apply T_False.
    - apply T_Zero.
    - apply T_Succ.
       + apply T_Zero.
Qed.

Example has_type_not :
  ~ (|- tif tfalse tzero ttrue \in TBool).
Proof.
  intros Contra. solve_by_inverts 2. Qed.

Example succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t \in TNat ->
  |- t \in TNat.
Proof.
  intros. inversion H. assumption.
Qed.


Lemma bool_canonical : forall t,
  |- t \in TBool -> value t -> bvalue t.
Proof.
  intros t HT HV.
  inversion HV; auto.
  induction H; inversion HT; auto.
Qed.

Lemma nat_canonical : forall t,
  |- t \in TNat -> value t -> nvalue t.
Proof.
  intros t HT HV.
  inversion HV.
  inversion H; subst; inversion HT.
  auto.
Qed.

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t => t'.
Proof with auto.
  intros t T HT.
  induction HT...
  (* The cases that were obviously values, like T_True and
     T_False, were eliminated immediately by auto *)
  - (* T_If *)
    right. inversion IHHT1; clear IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2...
      exists t3...
    + (* t1 can take a step *)
      inversion H as [t1' H1].
     exists (tif t1' t2 t3)...
  - (* T_Succ *)
    inversion IHHT.
    + left. apply (nat_canonical t1 HT) in H. auto.
    + inversion H. right. exists (tsucc x)...
  - (* T_Pred *)
    inversion IHHT.
    + right. apply (nat_canonical t1 HT) in H. inversion H.
      exists tzero... 
      exists t...
    + inversion H. right. exists (tpred x)...
  - (* T_Iszero *)
    right. inversion IHHT.  
    + apply (nat_canonical t1 HT) in H.  inversion H. 
      exists ttrue...
      exists tfalse...
    + inversion H. exists (tiszero x)...
Qed.

(*

Exercise: 3 stars, advanced (finish_progress_informal)
Complete the corresponding informal proof:
Theorem: If ⊢ t ∈ T, then either t is a value or else t => t' for some t'.
Proof: By induction on a derivation of ⊢ t ∈ T.

  If the last rule in the derivation is T_If, then t = if t1 then t2 else t3, with ⊢ t1 ∈ Bool,
    ⊢ t2 ∈ T and ⊢ t3 ∈ T. By the IH, either t1 is a value or else t1 can step to some t1'.

    If t1 is a value, then by the canonical forms lemmas and the fact that ⊢ t1 ∈ Bool we have
    that t1 is a bvalue — i.e., it is either true or false. If t1 = true, then t steps to t2 by ST_IfTrue, 
    while if t1 = false, then t steps to t3 by ST_IfFalse. Either way, t can step, which is what we wanted to 
    show.
    
    If t1 itself can take a step, then, by ST_If, so can t.

  If the laste rule in the derivation is T_Succ, then t = tsucc t1 with  ⊢ t1 ∈ Nat, By the IH
  either t1 is a value or else t1 can step to some t1'.
    
    If t1 is a value, then by the canonical forms lemma and the fact that |- t1 \in Nat we have
    that t1 is a nvalue. By apply nv_succ we know that tsucc t1 is also a nvalue, and a value.

    If t1 itself can take a step, then, by ST_Succ, so can t.

  If the last rule in the derivation is T_Pred, then t = tpred t1 with  ⊢ t1 ∈ Nat, By the IH
  either t1 is a value or else t1 can step to some t1'.

    If t1 is a value, then by the canonical forms lemma and the fact that |- t1 \in Nat we have
    that t1 is a nvalue. By inverse the nvalue, we know t1 should either be tzero or tsucc some t2 and t2
    is nvalue.
      
      If t1 is tzero, we know t is also tzero value by ST_PredZero.
      If t1 is tsucc t2, we know t is also nvalue by ST_PredSucc.
    
    If t1 can step to some t1', then we know that tpred t1 could step to pred t1' by ST_Pred.

  If the last rule in the derivation is T_Iszero, then t = tiszero t1 with  ⊢ t1 ∈ Nat, By the IH
  either t1 is a value or else t1 can step to some t1'.
    
    If t1 is value. then by the canonical forms lemma and the fact that |- t1 \in Nat we have
    that t1 is a nvalue. By analyze t1 we know t1 should either be tzero or tsucc of some t2.
      
      If ti is tzero we have t could step to tsuccse by ST_IszeroZero.
      If t1 is tsucc some t2, t oculd step to tfalse by ST_IszeroSucc.

    If t1 can step to some t1', then we know tiszero t1 could step to tiszero t1' by ST_Iszero.

  For else cases, they are just tzero/ttrue/tfalse which could be aproved.

Qed.
*)

(*

Exercise: 1 star (step_review)
Quick review: answer true or false. In this language...
Every well-typed normal form is a value.  
yes, immediate result of lemma progress.
Every value is a normal form.
yes.
The single-step reduction relation is a partial function (i.e., it is deterministic).
Yes. by lemma step_deterministic.
The single-step reduction relation is a total function.
No, some of the t in tm could be stuck.
*)


Theorem preservation : forall t t' T,
  |- t \in T ->
    t => t' ->
  |- t' \in T.

Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try solve_by_invert.
    - (* T_If *) inversion HE; subst; clear HE.
      + (* ST_IFTrue *) assumption.
      + (* ST_IfFalse *) assumption.
      + (* ST_If *) apply T_If; try assumption.
        apply IHHT1; assumption.
    - inversion HE; subst; clear HE. apply IHHT in H0. auto.
    - inversion HE; subst; clear HE.
      + auto.
      + clear IHHT. clear HT. induction H0; auto. 
      + apply IHHT in H0. auto.
    - inversion HE; subst; clear HE; auto.
Qed.

Theorem preservation' : forall t t' T,
  |- t \in T ->
    t => t' ->
  |- t' \in T.
Proof with auto.
  intros t t' T HT HE.
  generalize dependent T.
  induction HE; try (intros T HT; inversion HT; subst; clear HT; auto).
  clear H1.  induction H; auto.
Qed.

Definition multistep := (multi step).
Notation "t1 '=>*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t \in T ->
  t =>* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.
  apply IHP. apply (preservation x y T HT H).
  unfold stuck. split; auto. Qed. 

Notation " t '/' st '=>a*' t' " := (multi (astep st) t t')
                                    (at level 40, st at level 39).

Example astep_example1 :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  =>a* (ANum 15).
Proof.
  apply multi_step with (APlus (ANum 3) (ANum 12)).
    apply AS_Plus2.
      apply av_num.
      apply AS_Mult.
  apply multi_step with (ANum 15).
    apply AS_Plus.
  apply multi_refl.
Qed.

Hint Constructors astep aval.
Example astep_example1' :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  =>a* (ANum 15).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.

Tactic Notation "normalize" :=
   repeat (eapply multi_step ;
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply multi_refl.

Example astep_example1''' : exists e',
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  =>a* e'.
Proof.
  eapply ex_intro. normalize.
Qed.

Theorem normalize_ex : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state
  =>a* e'.
Proof.
  eapply ex_intro. normalize.
Qed.

Theorem subject_expansion_false:
  exists t t' T,
  t => t' -> |- t' \in T -> ~(|- t \in T).
Proof.
  exists (tif ttrue ttrue tzero), ttrue, TBool. intros. unfold not. intros. solve_by_inverts 2.
Qed.

(* variation 1
Determinism of step : yes
Progress:  false, example : tsucc ttrue has type TBool, but it's not a value and can't take step.
Preservation: true.
*)

(* variation 2
Determinism of step:  false, for example  (tif ttrue ttrue tfalse) could step to both ttrue and tfalse.
Progress: yes
Preservation: yes *)

(* variation 3

Determinism of step:  false
Progress: yes
Preservation: yes  *)

(* variation 4
Determinism of step:  yes
Progress: yes (ST_Funny3 can only apply to t without valid type)
Preservation: yes  *)

(* v5
Determinism of step:  yes
Progress: no (tif tzero ttrue tfalse) has valid type but stuck.
Preservation: no (tif ttrue tzero (tsucc tzero)) has type TNat but => TBool.
*)

(* v6.
Determinism of step:  yes
Progress: seems yes
Preservation: no, tpred tzero => tzero, tbool -> Tnat.
*)

(* remove_predzero

Determinism: yes
Progress: NO, tpred zero can't make progress
Preservation: yes
*)

(* prog_pres_bigstep
It should very similar to multi_step, but not reflective, so 
Progress: 
forall t T, |- t \in T -> value t \. exists t', t =>* t'.
Preservation:
Theorem preservation : forall t t' T,
  ⊢ t ∈ T →
  t ⇒* t' →
  ⊢ t' ∈ T.

*)