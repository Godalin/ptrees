Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Logic.ClassicalChoice Arith.PeanoNat.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting
  PTreeKernel PEutt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Internal computation laws, not an additional relation on programs.
    Exact witness equality is [sem_eq]; relational probability algebra
    uses [sem_lift eq].  The base interface does not identify these two.
    In particular, a coupling equation does not by itself license replacing
    the output argument of [stable_hitting]. *)
Section StableHeads.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}.

Lemma stable_hitting_ret_iff {R} (r : R) out :
  stable_hitting (@ptree_primitive_kernel E MN MF FI MX R) (observe (Ret r)) out <->
  sem_eq out (sem_ret (FHRet r)).
Proof.
  split.
  - intro Hhit. eapply stable_hitting_unique; [exact Hhit|].
    apply stable_hitting_ret.
  - intro Heq. unfold stable_hitting.
    eapply sem_lub_chain_proper with (chain := fun _ => out).
    + intro n. eapply sem_eq_trans; [exact Heq|].
      apply sem_eq_sym. unfold stable_hitting_approx, ptree_primitive_kernel.
      eapply sem_eq_trans; [apply sem_bind_ret_l|].
      rewrite stable_target_stableE. apply sem_eq_refl.
    + apply sem_lub_constant.
Qed.

Lemma stable_hitting_vis_iff {R X} (e : E X)
    (k : X -> ptree E MN R) out :
  stable_hitting (@ptree_primitive_kernel E MN MF FI MX R) (observe (Vis e k)) out <->
  sem_eq out (sem_ret (FHVis e k)).
Proof.
  split.
  - intro Hhit. eapply stable_hitting_unique; [exact Hhit|].
    apply stable_hitting_vis.
  - intro Heq. unfold stable_hitting.
    eapply sem_lub_chain_proper with (chain := fun _ => out).
    + intro n. eapply sem_eq_trans; [exact Heq|].
      apply sem_eq_sym. unfold stable_hitting_approx, ptree_primitive_kernel.
      eapply sem_eq_trans; [apply sem_bind_ret_l|].
      rewrite stable_target_stableE. apply sem_eq_refl.
    + apply sem_lub_constant.
Qed.

(** Tree-facing form: rewriting needs no preliminary unfolding of observe. *)
Lemma stable_hitting_tau {R} (t : ptree E MN R) out :
  stable_hitting (@ptree_primitive_kernel E MN MF FI MX R)
    (observe (Tau t)) out <->
  stable_hitting (@ptree_primitive_kernel E MN MF FI MX R) (observe t) out.
Proof. apply stable_hitting_tau_iff. Qed.

Lemma stable_hitting_tau_iter {R} n (t : ptree E MN R) out :
  stable_hitting (@ptree_primitive_kernel E MN MF FI MX R)
    (observe (Nat.iter n (fun u => Tau u) t)) out <->
  stable_hitting (@ptree_primitive_kernel E MN MF FI MX R) (observe t) out.
Proof.
  induction n as [|n IH]; [reflexivity|].
  change (stable_hitting (@ptree_primitive_kernel E MN MF FI MX R)
    (observe (Tau (Nat.iter n (fun u => Tau u) t))) out <->
    stable_hitting (@ptree_primitive_kernel E MN MF FI MX R) (observe t) out).
  rewrite stable_hitting_tau. exact IH.
Qed.
End StableHeads.

Section ProbabilityComputation.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{FI : SemanticMeasure MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.

(** Elimination uses complete branch limits, not a common finite bound.
    Introduction is [stable_hitting_prob], including its AE variant. *)
Theorem stable_hitting_prob_decompose {R X}
    (mu : MN X) (k : X -> ptree E MN R) out :
  stable_hitting (@ptree_primitive_kernel E MN MF FI MX R)
    (observe (Prob mu k)) out ->
  exists front : X -> MF (stable_head E MN R),
    (forall x, stable_hitting (@ptree_primitive_kernel E MN MF FI MX R)
      (observe (k x)) (front x)) /\
    sem_eq out (mixed_bind mu front).
Proof.
  intro Hhit.
  assert (Hex : forall x, exists out,
    stable_hitting (@ptree_primitive_kernel E MN MF FI MX R)
      (observe (k x)) out).
  { intro x. apply stable_hitting_exists. }
  destruct (choice _ Hex) as [front Hfront].
  exists front. split; [exact Hfront|].
  eapply stable_hitting_unique; [exact Hhit|].
  eapply stable_hitting_prob with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros x _. apply Hfront.
Qed.

Theorem stable_hitting_prob_compute {R X}
    (mu : MN X) (k : X -> ptree E MN R)
    (front : X -> MF (stable_head E MN R)) (Good : X -> Prop) out :
  sem_ae mu Good ->
  (forall x, Good x -> stable_hitting
    (@ptree_primitive_kernel E MN MF FI MX R) (observe (k x)) (front x)) ->
  stable_hitting (@ptree_primitive_kernel E MN MF FI MX R)
    (observe (Prob mu k)) out ->
  sem_eq out (mixed_bind mu front).
Proof.
  intros Hae Hfront Hhit. eapply stable_hitting_unique; [exact Hhit|].
  eapply stable_hitting_prob; eassumption.
Qed.

(** Dirac elimination at the abstraction strength actually supplied by
    [MixedMeasureUnitLaws]: equality coupling of complete outputs. *)
Theorem stable_hitting_prob_dirac {R X}
    `{MU : @MixedMeasureUnitLaws MN MF NI FI MX}
    (x : X) (k : X -> ptree E MN R) out1 out2 :
  stable_hitting (@ptree_primitive_kernel E MN MF FI MX R)
    (observe (Prob (sem_ret x) k)) out1 ->
  stable_hitting (@ptree_primitive_kernel E MN MF FI MX R)
    (observe (k x)) out2 ->
  sem_lift eq out1 out2.
Proof.
  intros H1 H2.
  destruct (stable_hitting_prob_decompose H1) as [front [Hfront Heq]].
  eapply sem_lift_proper_l; [apply sem_eq_sym; exact Heq|].
  eapply sem_lift_proper_r.
  - eapply stable_hitting_unique; [apply Hfront|exact H2].
  - apply mixed_bind_ret_l.
Qed.

(** Nested sampling is computed by two mixed binds.  The optional node-bind
    law then couples this result to the flattened native distribution. *)
Theorem stable_hitting_prob_flatten {R X Y}
    `{NB : @MixedMeasureNodeBindLaws MN MF NI FI MX}
    (mu : MN X) (h : X -> MN Y) (k : Y -> ptree E MN R) out1 out2 :
  stable_hitting (@ptree_primitive_kernel E MN MF FI MX R)
    (observe (Prob mu (fun x => Prob (h x) k))) out1 ->
  stable_hitting (@ptree_primitive_kernel E MN MF FI MX R)
    (observe (Prob (sem_bind mu h) k)) out2 ->
  sem_lift eq out1 out2.
Proof.
  intros H1 H2.
  destruct (stable_hitting_prob_decompose H2) as [front [Hfront Heq2]].
  assert (Heq1 : sem_eq out1
    (mixed_bind mu (fun x => mixed_bind (h x) front))).
  { eapply stable_hitting_prob_compute with (Good := fun _ => True).
    - apply sem_ae_true.
    - intros x _. eapply stable_hitting_prob with (Good := fun _ => True).
      + apply sem_ae_true.
      + intros y _. apply Hfront.
    - exact H1. }
  eapply sem_lift_proper_l; [apply sem_eq_sym; exact Heq1|].
  eapply sem_lift_proper_r; [apply sem_eq_sym; exact Heq2|].
  apply mixed_bind_node_assoc.
Qed.
End ProbabilityComputation.

Section BehavioralEndpoint.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}.

(** A derived existential presentation, not a change to the generator's
    bidirectional matching of all complete hitting witnesses. *)
Theorem peutt_iff_hitting {A B} (RR : A -> B -> Prop)
    (t : ptree E MN A) (u : ptree E MN B) :
  peutt RR t u <-> exists out1 out2,
    stable_hitting (@ptree_primitive_kernel E MN MF FI MX A) (observe t) out1 /\
    stable_hitting (@ptree_primitive_kernel E MN MF FI MX B) (observe u) out2 /\
    sem_lift (ptree_stable_head_rel RR
      (@peutt_state E MN MF FI FC MX FO A B RR)) out1 out2.
Proof.
  split.
  - intro Hrel.
    destruct (stable_hitting_exists
      (@ptree_primitive_kernel E MN MF FI MX A) (observe t)) as [out1 H1].
    destruct (stable_hitting_exists
      (@ptree_primitive_kernel E MN MF FI MX B) (observe u)) as [out2 H2].
    exists out1, out2. split; [exact H1|]. split; [exact H2|].
    eapply peutt_hitting_lift; eassumption.
  - intros [out1 [out2 [H1 [H2 Hlift]]]].
    eapply peutt_of_hitting_lift; eassumption.
Qed.
End BehavioralEndpoint.
