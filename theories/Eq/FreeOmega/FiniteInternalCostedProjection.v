Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Lia.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure FreeOmegaNative.
From PTree.Eq Require Import FiniteInternalPlan UnifiedFrontier PrimitiveStableHitting PTreeKernel.
From PTree.Eq.FreeOmega Require Import FiniteInternalNative FiniteInternalRound CostedKernel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A genuinely correlated native round can use a different compression
    plan at each whole state.  Its projected plan and costs need not factor
    through the projected tree.  The marginal premise is a QUOTIENT
    coupling of actual round paths preserving their cost and target.
    It need not reflect to a node lifting (NativeReflection refutes that
    stronger requirement).  Lifting a coupling of decoded residuals to
    these actual paths remains a separate obligation. *)
Section CostedProjection.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
  {R State Out : Type}.
Local Notation tree := (ptree E MN R).
Local Notation head := (stable_head E MN R).
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation hit := (@ptree_hitting_approx E MN MF FI FreeOmegaMixedMeasure
  FreeOmegaObservableSemanticOmega R).
Variable state_tree : State -> tree.
Variable output_head : Out -> head.
Variable plan : forall s, finite_internal_plan (state_tree s).
Variable X : State -> Type.
Variable measure : forall s, MN (X s).
Variable target : forall s, X s -> stable_target State Out.
Variable cost : forall s, X s -> nat.
Arguments target s _ : clear implicits.
Arguments cost s _ : clear implicits.

Definition costed_round_projection (z : stable_target State Out) : stable_target tree head :=
  match z with
  | SHStable o => SHStable (output_head o)
  | SHInternal s => SHInternal (state_tree s)
  end.

Definition costed_round_path_rel s x y : Prop :=
  cost s x = internal_round_steps (plan s) y /\
  costed_round_projection (target s x) =
    native_sample_value (internal_plan_round_native (plan s)) y.
Arguments costed_round_path_rel s x y : clear implicits.

Hypothesis round_marginal : forall s,
  free_omega_qlift (costed_round_path_rel s)
    (FOSample (measure s) (fun x => FORet x))
    (FOSample (native_sample_measure (internal_plan_round_native (plan s)))
      (fun y => FORet y)).

Lemma costed_round_progress_ae s :
  sem_ae (measure s) (fun x => forall u,
    target s x = SHInternal u -> 0 < cost s x).
Proof.
  assert (Hae : sem_ae (measure s)
    (fun x => exists y, costed_round_path_rel s x y /\ True)).
  { apply (proj1 (@free_omega_native_ae_iff MN NI NC (X s)
      {| native_sample_type := X s; native_sample_measure := measure s;
         native_sample_value := fun x => x |}
      (fun x => exists y, costed_round_path_rel s x y /\ True))).
    apply (proj2 (free_omega_qlift_support (round_marginal s)) (fun _ => True)).
    apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros x _. apply FOAERet. exact I. }
  eapply sem_ae_mono; [|exact Hae].
  intros x [y [[Hcost Htarget] _]] u Hu.
  rewrite Hcost. apply internal_round_progress with (u := state_tree u).
  rewrite <- Htarget, Hu. reflexivity.
Qed.

Lemma costed_round_reference fuel s :
  free_omega_qlift eq (hit fuel (observe (state_tree s)))
    (FOSample (measure s) (fun x =>
      if Nat.leb (cost s x) fuel then
        match target s x with
        | SHStable o => FORet (output_head o)
        | SHInternal u => hit (fuel - cost s x) (observe (state_tree u))
        end
      else FOZero)).
Proof.
  eapply FOQLComp with (T := eq) (U := eq);
    [exact (internal_round_hitting_approx (plan s) fuel)| |].
  - change (free_omega_qlift eq
      (free_omega_bind
        (FOSample (native_sample_measure (internal_plan_round_native (plan s)))
          (fun y => FORet y))
        (fun y => internal_target_budget fuel (internal_round_steps (plan s) y)
          (native_sample_value (internal_plan_round_native (plan s)) y)))
      (free_omega_bind (FOSample (measure s) (fun x => FORet x))
        (fun x => if Nat.leb (cost s x) fuel then
          match target s x with
          | SHStable o => FORet (output_head o)
          | SHInternal u => hit (fuel - cost s x) (observe (state_tree u))
          end else FOZero))).
    eapply FOQLBind with (T := fun y x => costed_round_path_rel s x y).
    + apply FOQLSym. exact (round_marginal s).
    + intros y x [Hcost Htarget]. unfold internal_target_budget.
      rewrite <- Hcost, <- Htarget.
      destruct (Nat.leb (cost s x) fuel); [destruct (target s x)|];
        cbn [costed_round_projection]; apply free_omega_qlift_refl;
        intro h; reflexivity.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

(** Complete marginal adequacy for arbitrarily recurring correlated
    rounds.  No structural reference marginal, unary policy, totality,
    or AST assumption occurs in this statement. *)
Theorem costed_round_projection_limit s :
  free_omega_qlift eq
    (FOLub (fun n => hit n (observe (state_tree s))))
    (free_omega_bind
      (FOLub (fun n => @stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
        State Out (costed_kernel measure target) n s))
      (fun o => FORet (output_head o))).
Proof.
  eapply costed_hitting_reference_limit with (cost := cost)
    (reference := fun n u => hit n (observe (state_tree u))).
  - exact NCAE.
  - exact NCountAE.
  - apply costed_round_progress_ae.
  - apply costed_round_reference.
Qed.

Theorem costed_round_stable_hitting s out joint_out :
  @ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R (observe (state_tree s)) out ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega State Out
    (costed_kernel measure target) s joint_out ->
  free_omega_qlift eq out
    (free_omega_bind joint_out (fun o => FORet (output_head o))).
Proof.
  intros Htree Hjoint.
  eapply FOQLComp with (T := eq) (U := eq); [exact Htree| |].
  - eapply FOQLComp with (T := eq) (U := eq); [apply costed_round_projection_limit| |].
    + eapply FOQLBind with (T := eq).
      * apply FOQLMono with (T := fun x y => y = x).
        -- apply FOQLSym. exact Hjoint.
        -- intros x y Hyx. symmetry. exact Hyx.
      * intros x y ->. apply FOQLStructural, FOLRet. reflexivity.
    + intros x z [y [-> ->]]. reflexivity.
  - intros x z [y [-> ->]]. reflexivity.
Qed.
End CostedProjection.
