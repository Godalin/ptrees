(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum rat.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Iteration.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import UnifiedFrontier PEutt.
From PTree.Semantics Require Import HeadTransition MDPFragment MDPEmbedding.
From PTree.Semantics Require Import TreeTransitionBisim.
From PTree.Semantics.Backend Require Import MDPEmbeddingSubEnumQ.
From PTree.Regression.Backend Require Import SubEnumQRegression.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory.
Local Open Scope ring_scope.

(** Infinitely many source states; every action has a genuinely random
    successor, and the two actions have different transition kernels.
    The count is internal: this instance has a constant unit observation. *)
Definition counter_next (n : nat) (action coin : bool) : nat :=
  if action then (n + if coin then 1 else 2)%nat
  else (n + if coin then 3 else 4)%nat.
Definition counter_step n a :=
  subenumQ_bind subenumQ_fair (fun b => subenumQ_ret (counter_next n a b)).

Lemma counter_step_total n a :
  @sem_total SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega _ (counter_step n a).
Proof.
  change (enumQ_expect (fun _ => 1)
    (bind_EnumQ (subenumQ_raw subenumQ_fair)
      (fun b => ret_EnumQ (counter_next n a b))) = 1).
  rewrite enumQ_expect_bind.
  native_compute. reflexivity.
Qed.

Definition counter_mdp : MDP SubEnumQ :=
  {| mdp_states := nat; mdp_actions := bool;
     mdp_observations := unit; mdp_observe := fun _ => tt;
     mdp_transition := counter_step; mdp_transition_total := counter_step_total |}.

Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).
Local Notation encode := (mdp_encode (D := counter_mdp)).
Local Notation ehead := (mdp_encode_head (D := counter_mdp)).
Local Notation pb := (@peutt (mdpE unit bool) SubEnumQ MF FI FC
  FreeOmegaMixedMeasure FO unit unit eq).

Example counter_encoding_is_mdp n :
  @mdp_state (mdpE unit bool) SubEnumQ MF FI FC FreeOmegaMixedMeasure FO unit (encode n).
Proof. exact (subenumQ_encode_mdp_state (D := counter_mdp) n). Qed.

Example counter_kernel_exact n a out :
  @head_step (mdpE unit bool) SubEnumQ MF FI FreeOmegaMixedMeasure FO unit
    (ehead n) (Obs (Choose tt) a) out <->
  @sem_eq MF FI _ out (FOSample (counter_step n a) (fun m => FORet (ehead m))).
Proof. exact (subenumQ_encode_step_iff (D := counter_mdp) n a out). Qed.

Example counter_full_abstraction n m :
  mdp_bisim (D := counter_mdp) n m <-> pb (encode n) (encode m).
Proof. exact (subenumQ_mdp_peutt_iff (D := counter_mdp) n m). Qed.

(** The new correspondence is not limited to finite state carriers. *)
Example counter_transition_full_abstraction n m :
  mdp_bisim (D := counter_mdp) n m <->
  @tree_trans_bisim (mdpE unit bool) SubEnumQ MF FI FC
    FreeOmegaMixedMeasure FO unit unit eq (encode n) (encode m).
Proof. exact (subenumQ_mdp_tree_trans_bisim_iff (D := counter_mdp) n m). Qed.

(** Intentional observability audit: source states are unlabelled, all
    actions are always enabled, and execution never terminates. Thus this
    model must not be advertised as distinguishing internal counter values.
    Constant observations recover the unlabelled baseline. *)
Theorem unlabelled_counter_states_bisimilar n m : mdp_bisim (D := counter_mdp) n m.
Proof.
  apply subenumQ_unlabelled_mdp_universal. intros u v. reflexivity.
Qed.

Example unlabelled_counter_encodings_equivalent n m : pb (encode n) (encode m).
Proof.
  apply (proj1 (subenumQ_mdp_peutt_iff (D := counter_mdp) n m)).
  apply unlabelled_counter_states_bisimilar.
Qed.
