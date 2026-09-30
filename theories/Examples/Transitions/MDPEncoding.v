(** Concrete labelled/unlabelled MDP encoding integration tests.
    Formal correspondence theorems remain in Semantics, not in this client. *)

From mathcomp Require ssreflect ssrbool ssralg ssrnum rat.
Require PTree.Core.PTreeDefinition.
Require PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require PTree.Prob.Backend.SubEnumQ.Measure PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Iteration.
Require PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require PTree.Eq.UnifiedFrontier PTree.Eq.PEutt.
Require PTree.Semantics.HeadTransition PTree.Semantics.MDPFragment PTree.Semantics.MDPEmbedding.
Require PTree.Semantics.TreeTransitionBisim.
Require PTree.Semantics.Backend.MDPEmbeddingSubEnumQ.
Require PTree.Examples.Probability.SubEnumQRegression.
Module MDPEmbedding.
(** Role: supporting program/semantic example, not a flagship claim. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import ssreflect ssrbool ssralg ssrnum rat.
Import PTree.Core.PTreeDefinition.
Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Import PTree.Prob.Backend.SubEnumQ.Measure PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Iteration.
Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Import PTree.Eq.UnifiedFrontier PTree.Eq.PEutt.
Import PTree.Semantics.HeadTransition PTree.Semantics.MDPFragment PTree.Semantics.MDPEmbedding.
Import PTree.Semantics.TreeTransitionBisim.
Import PTree.Semantics.Backend.MDPEmbeddingSubEnumQ.
Import PTree.Examples.Probability.SubEnumQRegression.
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
Local Notation pb := (@peutt (mdpE unit bool) SubEnumQ MF FI FC
  FreeOmegaMixedMeasure FO unit unit eq).

Example counter_encoding_is_mdp n :
  @mdp_state (mdpE unit bool) SubEnumQ MF FI FC FreeOmegaMixedMeasure FO unit (encode n).
Proof. exact (subenumQ_encode_mdp_state (D := counter_mdp) n). Qed.

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

End MDPEmbedding.

From mathcomp Require ssreflect ssrbool eqtype ssralg ssrnum rat.
Require PTree.Core.PTreeDefinition.
Require PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.SubEnumQ.Measure PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Iteration PTree.Prob.Backend.EnumQ.Coupling PTree.Prob.Backend.EnumQ.SemanticCoupling.
Require PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require PTree.Eq.PEutt.
Require PTree.Semantics.HeadTransition PTree.Semantics.MDPFragment PTree.Semantics.MDPEmbedding.
Require PTree.Semantics.TreeTransitionBisim.
Require PTree.Semantics.Backend.MDPEmbeddingSubEnumQ.
Require PTree.Examples.Probability.SubEnumQRegression.
Module LabelledMDP.
(** Role: supporting program/semantic example, not a flagship claim. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import ssreflect ssrbool eqtype ssralg ssrnum rat.
Import PTree.Core.PTreeDefinition.
Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Import PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.SubEnumQ.Measure PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Iteration PTree.Prob.Backend.EnumQ.Coupling PTree.Prob.Backend.EnumQ.SemanticCoupling.
Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Import PTree.Eq.PEutt.
Import PTree.Semantics.HeadTransition PTree.Semantics.MDPFragment PTree.Semantics.MDPEmbedding.
Import PTree.Semantics.TreeTransitionBisim.
Import PTree.Semantics.Backend.MDPEmbeddingSubEnumQ.
Import PTree.Examples.Probability.SubEnumQRegression.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory.
Local Open Scope ring_scope.

Inductive outcome_label := Running | Good | Bad.
Inductive labelled_state :=
  | StartHalf | StartBiased | StartClone | Good0 | Good1 | Bad0 | Bad1.

Definition state_label s :=
  match s with
  | StartHalf | StartBiased | StartClone => Running
  | Good0 | Good1 => Good
  | Bad0 | Bad1 => Bad
  end.

(** Good/Bad states continue forever with their own visible label. They
    are ordinary total states, not terminal states or hidden returns. *)
Definition labelled_step (s : labelled_state) (_ : unit) : SubEnumQ labelled_state :=
  match s with
  | StartHalf => subenumQ_bind subenumQ_fair (fun b => subenumQ_ret (if b then Good0 else Bad0))
  | StartClone => subenumQ_bind subenumQ_fair (fun b => subenumQ_ret (if b then Good1 else Bad1))
  | StartBiased => subenumQ_bind subenumQ_fair (fun b =>
      subenumQ_bind subenumQ_fair (fun c => subenumQ_ret (if b || c then Good0 else Bad0)))
  | _ => subenumQ_ret s
  end.

Lemma labelled_step_total s a :
  @sem_total SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega _ (labelled_step s a).
Proof. destruct s; native_compute; reflexivity. Qed.

Definition labelled_mdp : MDP SubEnumQ :=
  {| mdp_states := labelled_state; mdp_actions := unit;
     mdp_observations := outcome_label; mdp_observe := state_label;
     mdp_transition := labelled_step; mdp_transition_total := labelled_step_total |}.

Local Notation source_bisim := (mdp_bisim (D := labelled_mdp)).
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).
Local Notation encode := (mdp_encode (D := labelled_mdp)).
Local Notation pb := (@peutt (mdpE outcome_label unit) SubEnumQ MF FI FC
  FreeOmegaMixedMeasure FO unit unit eq).
Local Notation tb := (@trans_bisim (mdpE outcome_label unit) SubEnumQ MF FI FC
  FreeOmegaMixedMeasure FO unit unit eq).

Example labelled_encoding_in_fragment s :
  @mdp_state (mdpE outcome_label unit) SubEnumQ MF FI FC
    FreeOmegaMixedMeasure FO unit (encode s).
Proof. exact (subenumQ_encode_mdp_state (D := labelled_mdp) s). Qed.

Definition is_good_label l := match l with Good => true | _ => false end.
Definition is_good s := is_good_label (state_label s).
Definition good_probability s :=
  enumQ_expect (fun t => if is_good t then 1 else 0) (subenumQ_raw (labelled_step s tt)).

Example good_probability_half : good_probability StartHalf = 1 / 2.
Proof. native_compute. reflexivity. Qed.
Example good_probability_biased : good_probability StartBiased = 3 / 4.
Proof. native_compute. reflexivity. Qed.
Example good_probability_clone : good_probability StartClone = 1 / 2.
Proof. native_compute. reflexivity. Qed.

(** Even after the current observations agree, a coupling must preserve
    the probability of the next observation class. Project to the Boolean
    Good test, reflect its equality coupling to equality of finite masses,
    and compute the contradictory 1/2 = 3/4 equation. *)
Theorem different_successor_probabilities_not_bisimilar :
  ~ source_bisim StartHalf StartBiased.
Proof.
  intro H.
  pose proof (mdp_bisim_step H tt) as Hstep.
  assert (Htest : @sem_lift SubEnumQ SubEnumQ_SemanticMeasure bool bool eq
    (subenumQ_bind (labelled_step StartHalf tt) (fun s => subenumQ_ret (is_good s)))
    (subenumQ_bind (labelled_step StartBiased tt) (fun s => subenumQ_ret (is_good s)))).
  { eapply (@sem_lift_bind SubEnumQ SubEnumQ_SemanticMeasure
      SubEnumQ_SemanticMeasureBindLaws _ _ _ _ source_bisim); [exact Hstep|].
    intros s t Hst. apply (@sem_lift_ret SubEnumQ SubEnumQ_SemanticMeasure
      SubEnumQ_SemanticMeasureCoreLaws).
    exact (f_equal is_good_label (mdp_bisim_observe Hst)). }
  pose proof (Coupling.coupling_eq_enumQ_eq (enumQ_sem_lift_to_coupling Htest) true) as Hmass.
  change ((1 / 2 : rat) = 3 / 4) in Hmass.
  vm_compute in Hmass. discriminate.
Qed.

Example same_current_label_but_not_bisimilar :
  state_label StartHalf = state_label StartBiased /\
  ~ source_bisim StartHalf StartBiased.
Proof. split; [reflexivity|apply different_successor_probabilities_not_bisimilar]. Qed.

Theorem different_successor_probabilities_not_peutt :
  ~ pb (encode StartHalf) (encode StartBiased).
Proof.
  intro H. apply different_successor_probabilities_not_bisimilar.
  exact (proj2 (subenumQ_mdp_peutt_iff (D := labelled_mdp) StartHalf StartBiased) H).
Qed.

(** The positive example matches different successor STATES, not just
    differently named sources with identical kernels. Each matched pair
    has the same observation and continues within the candidate. *)
Inductive lump_pair : labelled_state -> labelled_state -> Prop :=
  | LumpStart : lump_pair StartHalf StartClone
  | LumpGood : lump_pair Good0 Good1
  | LumpBad : lump_pair Bad0 Bad1.

Theorem distinct_states_same_class_probabilities : source_bisim StartHalf StartClone.
Proof.
  eapply mdp_bisim_coinduction with (sim := lump_pair).
  - intros s t H. destruct H; split; try reflexivity; intro a.
    + eapply (@sem_lift_bind SubEnumQ SubEnumQ_SemanticMeasure
        SubEnumQ_SemanticMeasureBindLaws _ _ _ _ eq).
      * apply sem_lift_refl. intro b. reflexivity.
      * intros b c ->. apply (@sem_lift_ret SubEnumQ SubEnumQ_SemanticMeasure
          SubEnumQ_SemanticMeasureCoreLaws). destruct c; constructor.
    + apply (@sem_lift_ret SubEnumQ SubEnumQ_SemanticMeasure
        SubEnumQ_SemanticMeasureCoreLaws). constructor.
    + apply (@sem_lift_ret SubEnumQ SubEnumQ_SemanticMeasure
        SubEnumQ_SemanticMeasureCoreLaws). constructor.
  - constructor.
Qed.

Example positive_pair_is_not_state_equality : StartHalf <> StartClone.
Proof. discriminate. Qed.
Example positive_kernels_are_different :
  labelled_step StartHalf tt <> labelled_step StartClone tt.
Proof. intro H. pose proof (f_equal subenumQ_raw H) as Hraw. discriminate Hraw. Qed.

Theorem distinct_states_encoded_peutt : pb (encode StartHalf) (encode StartClone).
Proof.
  apply (proj1 (subenumQ_mdp_peutt_iff (D := labelled_mdp) StartHalf StartClone)).
  apply distinct_states_same_class_probabilities.
Qed.

(** The composed endpoint preserves actual labelled successor probabilities:
    the positive pair has different states/kernels, while the negative pair
    has the same current label but different next-label probabilities. *)
Example distinct_states_encoded_trans_bisimilar :
  tb (encode StartHalf) (encode StartClone).
Proof.
  apply (proj1 (subenumQ_mdp_trans_bisim_iff (D := labelled_mdp) StartHalf StartClone)).
  apply distinct_states_same_class_probabilities.
Qed.

Example different_successor_probabilities_not_trans_bisimilar :
  ~ tb (encode StartHalf) (encode StartBiased).
Proof.
  intro H. apply different_successor_probabilities_not_bisimilar.
  exact (proj2 (subenumQ_mdp_trans_bisim_iff (D := labelled_mdp) StartHalf StartBiased) H).
Qed.

(** The source now uses a DIFFERENT carrier: unbounded finite rational
    measures. The production adapter adds bound certificates to its total
    rows, and the generic representation theorem transports source bisim.
    Both probability-sensitive tests must survive this boundary. *)
Definition raw_labelled_mdp : MDP EnumQ :=
  {| mdp_states := labelled_state; mdp_actions := unit;
     mdp_observations := outcome_label; mdp_observe := state_label;
     mdp_transition := fun s a => subenumQ_raw (labelled_step s a);
     mdp_transition_total := labelled_step_total |}.

Local Lemma raw_labelled_bisim_iff s t :
  mdp_bisim (D := raw_labelled_mdp) s t <-> source_bisim s t.
Proof.
  exact (mdp_represent_bisim_iff (D := raw_labelled_mdp) labelled_step_total
    (fun rel s t a => iff_refl _) s t).
Qed.

Local Notation represented_encode :=
  (mdp_encode (D := enumQ_mdp_bounded raw_labelled_mdp)).

Example represented_positive_pair :
  tb (represented_encode StartHalf) (represented_encode StartClone).
Proof.
  apply (proj1 (enumQ_mdp_trans_bisim_iff (D := raw_labelled_mdp) _ _)).
  apply (proj2 (raw_labelled_bisim_iff _ _)).
  apply distinct_states_same_class_probabilities.
Qed.

Example represented_probability_separation :
  ~ tb (represented_encode StartHalf) (represented_encode StartBiased).
Proof.
  intro H. apply different_successor_probabilities_not_bisimilar.
  apply (proj1 (raw_labelled_bisim_iff _ _)).
  exact (proj2 (enumQ_mdp_trans_bisim_iff (D := raw_labelled_mdp) _ _) H).
Qed.

End LabelledMDP.
