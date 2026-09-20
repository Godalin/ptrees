Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum rat.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum
  DiscreteMC MeasureIterationEnum FreeOmegaMeasure.
From PTree.Eq Require Import UnifiedFrontier PEutt.
From PTree.Semantics Require Import HeadTransition MDPFragment
  MDPEmbedding MDPEmbeddingSubEnum.
From PTree.Examples Require Import SubEnumRegression.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum GRing.Theory.
Local Open Scope ring_scope.

(** Infinitely many source states; every action has a genuinely random
    successor, and the two actions have different transition kernels.
    The count is internal: the minimal source model has no state labels. *)
Definition counter_next (n : nat) (action coin : bool) : nat :=
  if action then (n + if coin then 1 else 2)%nat
  else (n + if coin then 3 else 4)%nat.
Definition counter_step n a :=
  subenum_bind subenum_fair (fun b => subenum_ret (counter_next n a b)).

Lemma counter_step_total n a :
  @sem_total SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega _ (counter_step n a).
Proof.
  change (enum_expect (fun _ => 1)
    (bind_Enum (subenum_raw subenum_fair)
      (fun b => ret_Enum (counter_next n a b))) = 1).
  rewrite enum_expect_bind /= !mulr1 !addr0.
  native_compute. reflexivity.
Qed.

Definition counter_mdp : MDP SubEnum :=
  {| mdp_states := nat; mdp_actions := bool;
     mdp_transition := counter_step; mdp_transition_total := counter_step_total |}.

Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
Local Notation encode := (mdp_encode (D := counter_mdp)).
Local Notation ehead := (mdp_encode_head (D := counter_mdp)).
Local Notation pb := (@peutt (mdpE bool) SubEnum MF FI FC
  FreeOmegaMixedMeasure FO unit unit eq).

Example counter_encoding_is_mdp n :
  @mdp_state (mdpE bool) SubEnum MF FI FC FreeOmegaMixedMeasure FO unit (encode n).
Proof. exact (subenum_encode_mdp_state (D := counter_mdp) n). Qed.

Example counter_kernel_exact n a out :
  @head_step (mdpE bool) SubEnum MF FI FreeOmegaMixedMeasure FO unit
    (ehead n) (Obs Choose a) out <->
  @sem_eq MF FI _ out (FOSample (counter_step n a) (fun m => FORet (ehead m))).
Proof. exact (subenum_encode_step_iff (D := counter_mdp) n a out). Qed.

Example counter_full_abstraction n m :
  mdp_bisim (D := counter_mdp) n m <-> pb (encode n) (encode m).
Proof. exact (subenum_mdp_peutt_iff (D := counter_mdp) n m). Qed.

(** Intentional observability audit: source states are unlabelled, all
    actions are always enabled, and execution never terminates. Thus this
    model must not be advertised as distinguishing internal counter values.
    Couple each transition using the same fresh coin, coinductively. *)
Theorem unlabelled_counter_states_bisimilar n m : mdp_bisim (D := counter_mdp) n m.
Proof.
  eapply mdp_bisim_coinduction with (sim := fun _ _ => True).
  - intros u v _ a. unfold mdp_bisimF. cbn [mdp_transition].
    eapply (@sem_lift_bind SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureBindLaws _ _ _ _ eq).
    + apply sem_lift_refl. intro b. reflexivity.
    + intros b c ->. apply (@sem_lift_ret SubEnum SubEnum_SemanticMeasure
        SubEnum_SemanticMeasureCoreLaws). exact I.
  - exact I.
Qed.

Example unlabelled_counter_encodings_equivalent n m : pb (encode n) (encode m).
Proof.
  apply (proj1 (subenum_mdp_peutt_iff (D := counter_mdp) n m)).
  apply unlabelled_counter_states_bisimilar.
Qed.
