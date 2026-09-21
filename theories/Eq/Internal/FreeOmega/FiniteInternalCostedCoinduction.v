(** Role: Internal execution/scheduling proof infrastructure. Supports hitting adequacy; not an additional behavioral equivalence. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Native.
From PTree.Eq.Internal Require Import FiniteInternalPlan.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternalNative FiniteInternalRound CostedKernel FiniteInternalCostedProjection.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A complete coinduction endpoint for a GIVEN correlated round process.
    The two marginals retain their actual compression paths and separate
    costs; they need not have structural reference couplings or unary
    compression policies.  Constructing such a joint from an arbitrary
    residual quotient coupling remains a separate obligation. *)
Section CostedCoinduction.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
  {A B State Out : Type}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Variable RR : A -> B -> Prop.
Variable sim : ptree E MN A -> ptree E MN B -> Prop.
Variable left_tree : State -> ptree E MN A.
Variable right_tree : State -> ptree E MN B.
Variable left_head : Out -> stable_head E MN A.
Variable right_head : Out -> stable_head E MN B.
Variable left_plan : forall s, finite_internal_plan (left_tree s).
Variable right_plan : forall s, finite_internal_plan (right_tree s).
Variable X : State -> Type.
Variable measure : forall s, MN (X s).
Variable target : forall s, X s -> stable_target State Out.
Variable left_cost right_cost : forall s, X s -> nat.
Arguments target s _ : clear implicits.

Hypothesis left_marginal : forall s,
  free_omega_qlift
    (costed_round_path_rel (state_tree := left_tree) (plan := left_plan)
      (s := s) left_head target left_cost)
    (FOSample (measure s) (fun x => FORet x))
    (FOSample (native_sample_measure (internal_plan_round_native (left_plan s)))
      (fun x => FORet x)).
Hypothesis right_marginal : forall s,
  free_omega_qlift
    (costed_round_path_rel (state_tree := right_tree) (plan := right_plan)
      (s := s) right_head target right_cost)
    (FOSample (measure s) (fun x => FORet x))
    (FOSample (native_sample_measure (internal_plan_round_native (right_plan s)))
      (fun x => FORet x)).

Let good_output o := stable_head_rel RR sim (left_head o) (right_head o).

(** Only emitted outputs need satisfy the head relation.  Internal
    successors are already states of the SAME correlated process. *)
Hypothesis round_closed : forall s, sem_ae (measure s) (fun x =>
  match target s x with SHStable o => good_output o | SHInternal _ => True end).

Lemma costed_round_joint_hitting_ae s out :
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega State Out
    (costed_kernel measure target) s out -> free_omega_ae good_output out.
Proof.
  intro Hhit. eapply (@stable_hitting_ae MF FI FreeOmegaObservableSemanticOmega
    FreeOmegaObservableSemanticMeasureAEKleisliLaws FreeOmegaObservableSemanticOmegaAELaws)
    with (D := fun _ => True).
  - intros state _. apply FOAESample with
      (Good := fun x => match target state x with
        SHStable o => good_output o | SHInternal _ => True end).
    + apply round_closed.
    + intros x Hx. apply FOAERet. exact Hx.
  - exact I.
  - exact Hhit.
Qed.

(** Complete hitting distributions are related even if the process
    diverges with positive probability; neither side is assumed AST. *)
Theorem costed_round_pair_hitting s out1 out2 :
  @ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A (observe (left_tree s)) out1 ->
  @ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega B (observe (right_tree s)) out2 ->
  free_omega_qlift (stable_head_rel RR sim) out1 out2.
Proof.
  intros Hhit1 Hhit2.
  pose (joint_out := FOLub (fun n => @stable_hitting_approx MF FI
    FreeOmegaObservableSemanticOmega State Out (costed_kernel measure target) n s)).
  assert (Hjoint : @stable_hitting MF FI FreeOmegaObservableSemanticOmega
    State Out (costed_kernel measure target) s joint_out).
  { apply free_omega_qlift_refl. intro o. reflexivity. }
  pose proof (costed_round_joint_hitting_ae Hjoint) as Hgood.
  assert (Hl : free_omega_qlift eq out1
    (free_omega_bind joint_out (fun o => FORet (left_head o)))).
  { eapply costed_round_stable_hitting with (plan := left_plan) (cost := left_cost).
    - exact left_marginal.
    - exact Hhit1.
    - exact Hjoint. }
  assert (Hr : free_omega_qlift eq out2
    (free_omega_bind joint_out (fun o => FORet (right_head o)))).
  { eapply costed_round_stable_hitting with (plan := right_plan) (cost := right_cost).
    - exact right_marginal.
    - exact Hhit2.
    - exact Hjoint. }
  eapply FOQLComp with (T := eq) (U := stable_head_rel RR sim); [exact Hl| |].
  - eapply FOQLComp with (T := stable_head_rel RR sim) (U := eq).
    + eapply FOQLBind with (T := fun o o' => o = o' /\ good_output o).
      * eapply FOQLAERestrict with (T := eq) (P := good_output) (Q := fun _ => True).
        -- apply free_omega_qlift_refl. intro o. reflexivity.
        -- exact Hgood.
        -- exact (@sem_ae_true MF FI FreeOmegaObservableSemanticMeasureCoreLaws
             Out joint_out).
        -- intros o o' [Heq [Ho _]]. split; assumption.
      * intros o o' [<- Ho]. apply FOQLStructural, FOLRet. exact Ho.
    + apply FOQLMono with (T := fun x y => y = x).
      * apply FOQLSym. exact Hr.
      * intros x y Hyx. symmetry. exact Hyx.
    + intros x z [y [Hxy ->]]. exact Hxy.
  - intros x z [y [-> Hyz]]. exact Hyz.
Qed.

(** Coverage connects the program candidate to the correlated state.
    State may retain the whole pair/history; no marginal policy is chosen. *)
Hypothesis covers : forall t u, sim t u ->
  exists s, left_tree s = t /\ right_tree s = u.

Theorem peutt_coinduction_costed_rounds t u :
  sim t u -> @peutt E MN MF FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega A B RR t u.
Proof.
  intro Hsim. eapply peutt_coinduction with
    (sim := fun s1 s2 => exists x y,
      s1 = observe x /\ s2 = observe y /\ sim x y).
  - intros s1 s2 [x [y [-> [-> Hxy]]]].
    destruct (covers Hxy) as [s [<- <-]].
    eapply stable_hitting_match_of_hitting_lift with
      (out1 := FOLub (fun n => @ptree_hitting_approx E MN MF FI
        FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega A n (observe (left_tree s))))
      (out2 := FOLub (fun n => @ptree_hitting_approx E MN MF FI
        FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega B n (observe (right_tree s)))).
    + apply free_omega_qlift_refl. intro h. reflexivity.
    + apply free_omega_qlift_refl. intro h. reflexivity.
    + eapply FOQLMono with (T := stable_head_rel RR sim).
      * apply costed_round_pair_hitting with (s := s).
        -- apply free_omega_qlift_refl. intro h. reflexivity.
        -- apply free_omega_qlift_refl. intro h. reflexivity.
      * intros h1 h2 Hheads. eapply stable_head_rel_mono; [|exact Hheads].
        intros a b Hab. exists a, b. repeat split; try reflexivity. exact Hab.
  - exists t, u. repeat split; try reflexivity. exact Hsim.
Qed.
End CostedCoinduction.
