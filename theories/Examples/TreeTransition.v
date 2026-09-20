Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Program.Equality Logic.FunctionalExtensionality.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum FreeOmegaMeasure
  MeasureIterationEnum.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel.
From PTree.Semantics Require Import HeadTransition TreeTransition.

(** The semantic API itself must remain independent of behavioral equality. *)
Fail Check PTree.Eq.PEutt.peutt.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum rat.
From PTree.Examples Require Import SubEnumRegression.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variant rawE : Type -> Type :=
  | Ask : rawE unit | Other : rawE unit
  | EmptyA : rawE Empty_set | EmptyB : rawE Empty_set.
Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
Local Notation head := (stable_head rawE SubEnum bool).
Local Notation tree := (ptree rawE SubEnum bool).
Local Notation trans := (@tree_trans rawE SubEnum MF FI FreeOmegaMixedMeasure FO bool).
Local Notation returns := (@tree_return_observation rawE SubEnum MF FI FreeOmegaMixedMeasure FO bool).
Local Notation offers := (@tree_offered_event_observation rawE SubEnum MF FI FreeOmegaMixedMeasure FO bool).
Local Notation hits t out := (@ptree_stable_hitting rawE SubEnum MF FI
  FreeOmegaMixedMeasure FO bool (observe t) out).

Example return_observation : returns (Ret true) (FORet true).
Proof. apply (tree_return_ret (FI := FI) (FO := FO)). Qed.
Example return_offers_nothing : offers (Ret true) FOZero.
Proof. apply (tree_offered_ret (FI := FI) (FO := FO)). Qed.
(** Zero in a totalized action subkernel does not assert an enabled action. *)
Example return_action_zero label : trans (Ret true) label FOZero.
Proof. apply (tree_trans_ret (FI := FI) (FO := FO)). Qed.

Definition deadA : tree := Vis EmptyA (fun x : Empty_set => match x with end).
Definition deadB : tree := Vis EmptyB (fun x : Empty_set => match x with end).
Example empty_a_observation : offers deadA (FORet (Offered EmptyA)).
Proof. apply (tree_offered_vis (FI := FI) (FO := FO)). Qed.
Example empty_b_observation : offers deadB (FORet (Offered EmptyB)).
Proof. apply (tree_offered_vis (FI := FI) (FO := FO)). Qed.

Lemma empty_offers_distinct :
  ~ @sem_lift MF FI _ _ eq (FORet (Offered EmptyA)) (FORet (Offered EmptyB)).
Proof.
  intro H.
  assert (Ha : free_omega_ae (NI := SubEnum_SemanticMeasure)
      (fun e => e = Offered EmptyA) (FORet (Offered EmptyA))).
  { constructor. reflexivity. }
  pose proof (proj1 (free_omega_qlift_support H) _ Ha) as Hb.
  dependent destruction Hb. destruct H0 as [a [-> Hbad]]. discriminate.
Qed.

Theorem empty_events_have_no_common_observation out :
  offers deadA out -> offers deadB out -> False.
Proof.
  intros Ha Hb. apply empty_offers_distinct.
  pose proof (tree_head_observation_unique empty_a_observation Ha) as Hleft.
  pose proof (tree_head_observation_unique Hb empty_b_observation) as Hright.
  eapply sem_lift_mono; [|eapply sem_lift_comp; [exact Hleft|exact Hright]].
  intros a b [c [-> ->]]. reflexivity.
Qed.

Example empty_a_action_zero label : trans deadA label FOZero.
Proof.
  apply (tree_trans_vis_miss (FI := FI) (FO := FO)).
  intro H. dependent destruction H. destruct x.
Qed.
Example empty_b_action_zero label : trans deadB label FOZero.
Proof.
  apply (tree_trans_vis_miss (FI := FI) (FO := FO)).
  intro H. dependent destruction H. destruct x.
Qed.

Definition ask_head b : head := FHVis Ask (fun _ => Ret b).
Definition other_head : head := FHVis Other (fun _ => Ret true).
Definition mixture : tree :=
  Prob subenum_fair (fun b => if b then Vis Other (fun _ => Ret true)
    else Prob subenum_fair (fun c => Vis Ask (fun _ => Ret c))).
Definition mixed_front : MF head :=
  FOSample subenum_fair (fun b => if b then FORet other_head
    else FOSample subenum_fair (fun c => FORet (ask_head c))).
Definition mixed_out : MF head :=
  FOSample subenum_fair (fun b => if b then FOZero
    else FOSample subenum_fair (fun c => FORet (FHRet c))).

Lemma mixture_hitting : hits mixture mixed_front.
Proof.
  unfold mixture, mixed_front.
  eapply (ptree_stable_hitting_prob (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros [|] _.
    + apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)).
    + eapply (ptree_stable_hitting_prob (FI := FI) (FO := FO)
        (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros c _. apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)).
Qed.

(** A witness only on this example's supported heads, not a general evaluator. *)
Definition follow_ask (h : head) : MF head :=
  match h with
  | FHRet _ => FOZero
  | @FHVis _ _ _ X e k =>
      (match e in rawE X return (X -> tree) -> MF head with
       | Ask => fun k => match observe (k tt) with
           | RetF r => FORet (FHRet r) | _ => FOZero end
       | Other => fun _ => FOZero
       | EmptyA => fun _ => FOZero
       | EmptyB => fun _ => FOZero
       end) k
  end.

Theorem mixture_action_weighted_sum : trans mixture (Obs Ask tt) mixed_out.
Proof.
  assert (Hae : @sem_ae MF FI head mixed_front
    (fun h => @head_action_result rawE SubEnum MF FI FreeOmegaMixedMeasure FO bool
      (Obs Ask tt) h (follow_ask h))).
  { eapply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros [|] _; cbn.
    - apply FOAERet. apply HARMiss.
      + intro H. dependent destruction H.
      + apply sem_eq_refl.
    - eapply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
      intros c _. apply FOAERet. apply HARMatch. constructor.
      apply (ptree_stable_hitting_ret (FI := FI) (FO := FO)). }
  assert (Heq : free_omega_bind mixed_front follow_ask = mixed_out).
  { unfold mixed_front, mixed_out. cbn. f_equal.
    extensionality b. destruct b; reflexivity. }
  rewrite <- Heq. exact (tree_trans_from_hitting mixture_hitting Hae).
Qed.

Example delayed_mixture_same_transition : trans (Tau mixture) (Obs Ask tt) mixed_out.
Proof.
  apply (proj2 (tree_trans_tau_iff (FI := FI) (FO := FO) _ _ _)).
  exact mixture_action_weighted_sum.
Qed.

Definition head_bool (h : head) :=
  match h with FHRet r => r | @FHVis _ _ _ _ _ _ => false end.
Definition mixed_native : SubEnum bool :=
  subenum_bind subenum_fair (fun b => if b then subenum_zero
    else subenum_bind subenum_fair (fun c => subenum_ret c)).

Lemma mixture_numeric_observation :
  free_omega_observes (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)
    head_bool mixed_out mixed_native.
Proof.
  unfold mixed_out, mixed_native.
  change (free_omega_observes head_bool
    (FOSample subenum_fair (fun b => if b then FOZero
      else FOSample subenum_fair (fun c => FORet (FHRet c))))
    (@sem_bind SubEnum SubEnum_SemanticMeasure bool bool subenum_fair
      (fun b => if b then subenum_zero
        else subenum_bind subenum_fair (fun c => subenum_ret c)))).
  apply FOOObserveSample. intros [|].
  - exact (@FOOObserveZero SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega
      head bool head_bool).
  - change (free_omega_observes head_bool
      (FOSample subenum_fair (fun c => FORet (FHRet c)))
      (@sem_bind SubEnum SubEnum_SemanticMeasure bool bool subenum_fair subenum_ret)).
    apply FOOObserveSample. intro c.
    exact (@FOOObserveRet SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega
      head bool head_bool (FHRet c)).
Qed.

Import GRing.Theory.
Local Open Scope ring_scope.
Example mixture_mass_not_normalized : enum_mass (subenum_raw mixed_native) = (1 / 2 : rat).
Proof. native_compute. reflexivity. Qed.
Example mixture_true_mass :
  enum_expect (fun b => if b then 1 else 0) (subenum_raw mixed_native) = (1 / 4 : rat).
Proof. native_compute. reflexivity. Qed.
Example mixture_false_mass :
  enum_expect (fun b => if b then 0 else 1) (subenum_raw mixed_native) = (1 / 4 : rat).
Proof. native_compute. reflexivity. Qed.
