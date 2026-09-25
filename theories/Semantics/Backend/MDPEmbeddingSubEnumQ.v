(** Role: Comparison semantics. Depends on canonical theory; not the canonical peutt relation or interpreter theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Eq Require Import StableHittingRelation.
From Coq.Program Require Import Equality.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum rat.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure PTree.Prob.Backend.EnumQ.Iteration PTree.Prob.Backend.EnumQ.Representation.
From PTree.Prob.Interface Require Import SemanticCoupling.
Require Import PTree.Prob.Backend.EnumQ.Disintegration.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Native PTree.Prob.FreeOmega.NativeCoupling.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.NativeCoupling.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.
From PTree.Semantics Require Import HeadTransition MDPFragment MDPEmbedding.
From PTree.Semantics Require Import TreeTransitionBisim MDPReflection.
From PTree.Semantics.FreeOmega Require Import MDPCoincidenceFreeOmega.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory.
Local Open Scope ring_scope.

Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).

(** Reuse the proved native-coupling realization capability. The decoding
    functions need NOT be injective; two source states may have identical
    encodings. Native carriers need NOT be finite types: SubEnumQ measures
    have finite support, including on infinite source state spaces. *)
Lemma subenumQ_sampled_heads_reflect {X Y A B}
    (mu : SubEnumQ X) (nu : SubEnumQ Y) (f : X -> A) (g : Y -> B)
    (R : A -> B -> Prop) :
  free_omega_qlift R (FOSample mu (fun x => FORet (f x)))
    (FOSample nu (fun y => FORet (g y))) ->
  @sem_lift SubEnumQ SubEnumQ_SemanticMeasure _ _ (fun x y => R (f x) (g y)) mu nu.
Proof.
  exact: free_omega_sampled_heads_reflect.
Qed.

Lemma subenumQ_dirac_heads_reflect {A B} (R : A -> B -> Prop) x y :
  @free_omega_qlift SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    A B R (FORet x) (FORet y) -> R x y.
Proof.
  intro H.
  assert (Hx : free_omega_ae (fun a => a = x) (FORet x)).
  { constructor. reflexivity. }
  pose proof (proj1 (free_omega_qlift_support H) _ Hx) as Hy.
  dependent destruction Hy. destruct H0 as [z [Hz ->]]. exact Hz.
Qed.

Lemma subenumQ_total_forget {X} (mu : SubEnumQ X) :
  @sem_total SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega _ mu ->
  @sem_total SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega _
    (subenumQ_bind mu (fun _ => subenumQ_ret tt)).
Proof.
  intro H. change (enumQ_expect (fun _ => 1)
    (bind_EnumQ (subenumQ_raw mu) (fun _ => ret_EnumQ tt)) = 1).
  rewrite enumQ_expect_bind enumQ_expect_ret. exact H.
Qed.

Section Embedding.
Variable D : MDP SubEnumQ.
Local Notation encode := (mdp_encode (D := D)).
Local Notation ehead := (mdp_encode_head (D := D)).
Local Notation successors := (@mdp_successors SubEnumQ SubEnumQ_SemanticMeasure
  SubEnumQ_SemanticOmega D MF FI FreeOmegaMixedMeasure).
Local Notation hb := (@head_bisim (mdpE (mdp_observations D) (mdp_actions D)) SubEnumQ MF FI FC
  FreeOmegaMixedMeasure FO unit unit eq).
Local Notation pb := (@peutt (mdpE (mdp_observations D) (mdp_actions D)) SubEnumQ MF FI FC
  FreeOmegaMixedMeasure FO unit unit eq).
Local Notation hits t out := (@ptree_stable_hitting (mdpE (mdp_observations D) (mdp_actions D))
  SubEnumQ MF FI FreeOmegaMixedMeasure FO unit (observe t) out).

Theorem subenumQ_encode_mdp_state s :
  @mdp_state (mdpE (mdp_observations D) (mdp_actions D)) SubEnumQ MF FI FC
    FreeOmegaMixedMeasure FO unit (encode s).
Proof.
  apply (mdp_encode_mdp_state (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)).
  - intros t a. apply free_omega_observable_total_intro.
    exists unit, (fun _ => tt),
      (subenumQ_bind (mdp_transition D t a) (fun _ => subenumQ_ret tt)).
    split.
    + change (free_omega_observes (NI := SubEnumQ_SemanticMeasure)
        (fun _ => tt) (FOSample (mdp_transition D t a) (fun u => FORet (ehead u)))
        (@sem_bind SubEnumQ SubEnumQ_SemanticMeasure _ _ (mdp_transition D t a)
          (fun _ => subenumQ_ret tt))).
      eapply FOOObserveSample. intro u. constructor.
    + apply subenumQ_total_forget. apply mdp_transition_total.
  - intros t a. eapply FOAESample with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros u _. constructor. exists u. reflexivity.
Qed.

(** This concrete backend also makes hitting closed under semantic
    equality of outputs, giving the literal iff for arbitrary targets. *)
Theorem subenumQ_encode_step_iff s a out :
  @head_step (mdpE (mdp_observations D) (mdp_actions D)) SubEnumQ MF FI FreeOmegaMixedMeasure FO unit
    (ehead s) (Obs (Choose (mdp_observe D s)) a) out <->
  @sem_eq MF FI _ out (successors (mdp_transition D s a)).
Proof.
  exact (mdp_encode_step_iff (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    (D := D) (@free_omega_observable_lub_limit_proper
      SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticMeasureCoreLaws SubEnumQ_SemanticOmega)
    s a out).
Qed.

Theorem subenumQ_head_bisim_reflect s t : hb (ehead s) (ehead t) -> mdp_bisim (D := D) s t.
Proof.
  exact (mdp_head_bisim_reflect (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure) (@subenumQ_sampled_heads_reflect) (D := D) (s := s) (t := t)).
Qed.

Theorem subenumQ_mdp_head_bisim_iff s t : mdp_bisim (D := D) s t <-> hb (ehead s) (ehead t).
Proof.
  split; [apply (mdp_bisim_head_sound (FI := FI) (FO := FO))|apply subenumQ_head_bisim_reflect].
Qed.

Lemma subenumQ_encoded_vis_inversion s t : pb (encode s) (encode t) ->
  mdp_observe D s = mdp_observe D t /\
  forall a, pb (Prob (mdp_transition D s a) encode)
    (Prob (mdp_transition D t a) encode).
Proof.
  exact (mdp_encoded_vis_inversion (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure) (FD := free_omega_observable_dirac_ae_laws)
    (D := D) (s := s) (t := t)).
Qed.

Theorem subenumQ_peutt_mdp_reflect s t : pb (encode s) (encode t) -> mdp_bisim (D := D) s t.
Proof.
  exact (mdp_peutt_reflect (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure) (FD := free_omega_observable_dirac_ae_laws)
    (@subenumQ_sampled_heads_reflect) (D := D) (s := s) (t := t)).
Qed.

Theorem subenumQ_mdp_peutt_iff s t : mdp_bisim (D := D) s t <-> pb (encode s) (encode t).
Proof.
  split; [apply (mdp_bisim_peutt_sound (FI := FI) (FO := FO))|apply subenumQ_peutt_mdp_reflect].
Qed.

(** Classical correspondence on encoded labelled MDPs. Native reflection
    gives the first iff; fragment membership discharges BOTH premises of
    the second. No finite-state or injective-encoding premise is required.
    This does not identify the two tree relations outside the MDP fragment. *)
Theorem subenumQ_mdp_tree_trans_bisim_iff s t :
  mdp_bisim (D := D) s t <->
  @tree_trans_bisim (mdpE (mdp_observations D) (mdp_actions D))
    SubEnumQ MF FI FC FreeOmegaMixedMeasure FO unit unit eq (encode s) (encode t).
Proof.
  rewrite subenumQ_mdp_peutt_iff.
  apply (free_mdp_state_peutt_tree_trans_iff (NI := SubEnumQ_SemanticMeasure)
    (NO := SubEnumQ_SemanticOmega)); apply subenumQ_encode_mdp_state.
Qed.

Corollary subenumQ_encoded_head_peutt_iff s t :
  hb (ehead s) (ehead t) <-> pb (encode s) (encode t).
Proof. rewrite <- subenumQ_mdp_head_bisim_iff, <- subenumQ_mdp_peutt_iff. reflexivity. Qed.

(** The old unlabelled baseline is recovered by CONSTANT observations.
    This is not true for arbitrary labelled MDPs. *)
Theorem subenumQ_unlabelled_mdp_universal
    (Hconstant : forall s t, mdp_observe D s = mdp_observe D t)
    s t : mdp_bisim (D := D) s t.
Proof.
  eapply mdp_bisim_coinduction with (sim := fun _ _ => True).
  - intros u v _. split; [apply Hconstant|]. intro a.
    eapply sem_lift_mono with
      (R := fun _ _ => exists z : unit, True /\ True).
    + intros x y _. exact I.
    + eapply sem_lift_comp with (nu := subenumQ_ret tt).
      * apply subenumQ_total_same_mass. exact (mdp_transition_total D u a).
      * apply sem_lift_sym. apply subenumQ_total_same_mass. exact (mdp_transition_total D v a).
  - exact I.
Qed.
End Embedding.
