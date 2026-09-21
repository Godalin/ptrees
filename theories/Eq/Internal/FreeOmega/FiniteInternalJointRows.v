(** Role: Internal execution/scheduling proof infrastructure. Supports hitting adequacy; not an additional behavioral equivalence. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Logic Require Import ClassicalDescription IndefiniteDescription.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Native.
From PTree.Eq.Internal Require Import FiniteInternalPlan.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PEutt.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternalNative FiniteInternalRound FiniteInternalRoundCoupling FiniteInternalCostedProjection FiniteInternalCostedCoinduction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** From per-pair joint rows to a recurring correlated process.  Neither
    transitivity of the candidate nor a unary marginal policy is needed.
    The rows are genuine measures, with both quotient graph marginals;
    supported partners are never selected in place of random samples. *)
Section JointCoinduction.
Universes node node_rep frontier.
Context {E : Type -> Type} {MN : Type@{node} -> Type@{node_rep}}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI} {A B : Type}.
Variable RR : A -> B -> Prop.
Variable sim : ptree E MN A -> ptree E MN B -> Prop.
Let treeA : Type@{frontier} := ptree E MN A.
Let treeB : Type@{frontier} := ptree E MN B.
Local Notation qlift := (@free_omega_qlift@{
  frontier frontier node node node node node node node node node node frontier frontier frontier
  node node node node node_rep node node node node node node node node
  node node node node node node node node node node} MN NI NO _ _).

Record finite_internal_joint_row (t : treeA) (u : treeB) := {
  joint_row_left_plan : finite_internal_plan t;
  joint_row_right_plan : finite_internal_plan u;
  joint_row_sample : Type@{node};
  joint_row_measure : MN joint_row_sample;
  joint_row_left : joint_row_sample ->
    native_sample_type (internal_plan_round_native joint_row_left_plan);
  joint_row_right : joint_row_sample ->
    native_sample_type (internal_plan_round_native joint_row_right_plan);
  joint_row_left_marginal : qlift (fun z x => joint_row_left z = x)
    (FOSample joint_row_measure (fun z => FORet z))
    (FOSample (native_sample_measure (internal_plan_round_native joint_row_left_plan))
      (fun x => FORet x));
  joint_row_right_marginal : qlift (fun z y => joint_row_right z = y)
    (FOSample joint_row_measure (fun z => FORet z))
    (FOSample (native_sample_measure (internal_plan_round_native joint_row_right_plan))
      (fun y => FORet y));
  joint_row_related : sem_ae joint_row_measure (fun z =>
    internal_round_path_rel RR sim joint_row_left_plan joint_row_right_plan
      (joint_row_left z) (joint_row_right z))
}.

Hypothesis rows_exist : forall t u, sim t u -> inhabited (finite_internal_joint_row t u).

Definition joint_state := { pair : treeA * treeB | sim (fst pair) (snd pair) }.
Definition joint_left_tree (s : joint_state) := fst (proj1_sig s).
Definition joint_right_tree (s : joint_state) := snd (proj1_sig s).
Definition chosen_joint_row (s : joint_state) :
  finite_internal_joint_row (joint_left_tree s) (joint_right_tree s).
Proof.
  refine (proj1_sig (constructive_indefinite_description
    (fun _ : finite_internal_joint_row (joint_left_tree s) (joint_right_tree s) => True) _)).
  destruct (rows_exist (proj2_sig s)) as [row]. exists row. exact I.
Defined.

Let left_plan s := joint_row_left_plan (chosen_joint_row s).
Let right_plan s := joint_row_right_plan (chosen_joint_row s).
Let samples s := joint_row_sample (chosen_joint_row s).
Let measure s := joint_row_measure (chosen_joint_row s).
Let project_left s := @joint_row_left _ _ (chosen_joint_row s).
Let project_right s := @joint_row_right _ _ (chosen_joint_row s).
Arguments project_left s _ : clear implicits.
Arguments project_right s _ : clear implicits.
Let head_pair := (stable_head E MN A * stable_head E MN B)%type.

(** The fallback is used only on null/unsupported samples.  It remains
    inside the state space, so no arbitrary default program is needed. *)
Definition paired_target (fallback : joint_state)
    (x : stable_target treeA (stable_head E MN A))
    (y : stable_target treeB (stable_head E MN B)) : stable_target joint_state head_pair :=
  match x, y with
  | SHStable h, SHStable k => SHStable (h,k)
  | SHInternal t, SHInternal u =>
      match excluded_middle_informative (sim t u) with
      | left H => SHInternal (exist _ (t,u) H)
      | right _ => SHInternal fallback
      end
  | _, _ => SHInternal fallback
  end.

Lemma paired_target_projections s x y : internal_round_target_rel RR sim x y ->
  costed_round_projection joint_left_tree (@fst _ _) (paired_target s x y) = x /\
  costed_round_projection joint_right_tree (@snd _ _) (paired_target s x y) = y.
Proof.
  destruct x as [h|t], y as [k|u]; cbn [internal_round_target_rel paired_target]; try contradiction.
  - intro H. split; reflexivity.
  - intro H. destruct (excluded_middle_informative (sim t u));
      [split; reflexivity|contradiction].
Qed.

Lemma paired_target_closed s x y : internal_round_target_rel RR sim x y ->
  match paired_target s x y with
  | SHStable heads => stable_head_rel RR sim (fst heads) (snd heads)
  | SHInternal _ => True
  end.
Proof.
  destruct x as [h|t], y as [k|u]; cbn [internal_round_target_rel paired_target]; try contradiction.
  - exact (fun H => H).
  - intro H. destruct (excluded_middle_informative (sim t u)); exact I.
Qed.

Definition joint_target s (z : samples s) := paired_target s
  (native_sample_value (internal_plan_round_native (left_plan s)) (project_left s z))
  (native_sample_value (internal_plan_round_native (right_plan s)) (project_right s z)).
Definition joint_left_cost s (z : samples s) := internal_round_steps (left_plan s) (project_left s z).
Definition joint_right_cost s (z : samples s) := internal_round_steps (right_plan s) (project_right s z).

Lemma chosen_joint_left_marginal s :
  qlift (costed_round_path_rel (state_tree := joint_left_tree) (plan := left_plan)
    (s := s) (@fst _ _) joint_target joint_left_cost)
    (FOSample (measure s) (fun z => FORet z))
    (FOSample (native_sample_measure (internal_plan_round_native (left_plan s))) (fun x => FORet x)).
Proof.
  eapply FOQLAERestrict with (T := fun z x => project_left s z = x)
    (P := fun z => internal_round_path_rel RR sim (left_plan s) (right_plan s)
      (project_left s z) (project_right s z)) (Q := fun _ => True).
  - exact (joint_row_left_marginal (chosen_joint_row s)).
  - apply FOAESample with (Good := fun z => internal_round_path_rel RR sim
      (left_plan s) (right_plan s) (project_left s z) (project_right s z)).
    + exact (joint_row_related (chosen_joint_row s)).
    + intros z Hz. apply FOAERet. exact Hz.
  - apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros x _. apply FOAERet. exact I.
  - intros z x [<- [Hz _]]. split; [reflexivity|].
    exact (proj1 (paired_target_projections s Hz)).
Qed.

Lemma chosen_joint_right_marginal s :
  qlift (costed_round_path_rel (state_tree := joint_right_tree) (plan := right_plan)
    (s := s) (@snd _ _) joint_target joint_right_cost)
    (FOSample (measure s) (fun z => FORet z))
    (FOSample (native_sample_measure (internal_plan_round_native (right_plan s))) (fun x => FORet x)).
Proof.
  eapply FOQLAERestrict with (T := fun z x => project_right s z = x)
    (P := fun z => internal_round_path_rel RR sim (left_plan s) (right_plan s)
      (project_left s z) (project_right s z)) (Q := fun _ => True).
  - exact (joint_row_right_marginal (chosen_joint_row s)).
  - apply FOAESample with (Good := fun z => internal_round_path_rel RR sim
      (left_plan s) (right_plan s) (project_left s z) (project_right s z)).
    + exact (joint_row_related (chosen_joint_row s)).
    + intros z Hz. apply FOAERet. exact Hz.
  - apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros x _. apply FOAERet. exact I.
  - intros z x [<- [Hz _]]. split; [reflexivity|].
    exact (proj2 (paired_target_projections s Hz)).
Qed.

Theorem peutt_coinduction_joint_rows t u : sim t u ->
  @peutt E MN (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A B RR t u.
Proof.
  intro Htu. eapply peutt_coinduction_costed_rounds with
    (sim := sim) (left_tree := joint_left_tree) (right_tree := joint_right_tree)
    (left_head := @fst _ _) (right_head := @snd _ _)
    (left_plan := left_plan) (right_plan := right_plan)
    (measure := measure) (target := joint_target)
    (left_cost := joint_left_cost) (right_cost := joint_right_cost).
  - apply chosen_joint_left_marginal.
  - apply chosen_joint_right_marginal.
  - intro s. eapply sem_ae_mono; [|exact (joint_row_related (chosen_joint_row s))].
    intros z Hz. exact (paired_target_closed s Hz).
  - intros x y Hxy. exists (exist _ (x,y) Hxy). split; reflexivity.
  - exact Htu.
Qed.
End JointCoinduction.
