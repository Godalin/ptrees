(** Role: Internal execution/scheduling proof infrastructure. Supports hitting adequacy; not an additional behavioral equivalence. *)
Set Universe Polymorphism.
(** Unit-valued guard samples must not specialize the helper lemmas to
    Set: plan paths and their PTree-valued decoders remain polymorphic. *)
Local Unset Universe Minimization ToSet.
From Coq.Arith Require Import PeanoNat.
From Coq Require Import Lia.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure FreeOmegaNative.
From PTree.Eq.Internal Require Import FiniteInternalPlan.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternalNative FiniteInternalPlanHitting.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The exact internal cost of a full compression-plus-guard round.
    A stable guard costs zero (Ret/Vis are already observable), whereas
    a Tau/Prob guard costs one.  This distinction enforces real progress
    whenever the round recursively continues with another tree. *)
Section RoundCosts.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI} {R : Type}.
Local Notation tree := (ptree E MN R).
Local Notation head := (stable_head E MN R).
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation hit := (@ptree_hitting_approx E MN MF FI FreeOmegaMixedMeasure
  FreeOmegaObservableSemanticOmega R).

Definition internal_guard_steps (t : tree) : nat :=
  match observe t with RetF _ | VisF _ _ _ => 0 | TauF _ | ProbF _ _ _ => 1 end.

Lemma internal_guard_progress t x u :
  native_sample_value (internal_guard_native t) x = SHInternal u ->
  0 < internal_guard_steps t.
Proof.
  unfold internal_guard_native, internal_guard_steps in *.
  destruct (observe t); cbn in *; intro H; try discriminate; lia.
Qed.

Definition internal_round_steps {t} (p : @finite_internal_plan E MN R t)
    (z : native_sample_type (internal_plan_round_native p)) : nat :=
  internal_plan_steps p (projT1 z) +
    internal_guard_steps (internal_plan_residual p (projT1 z)).
Arguments internal_round_steps {t} p _.

Theorem internal_round_progress t (p : @finite_internal_plan E MN R t) z u :
  native_sample_value (internal_plan_round_native p) z = SHInternal u ->
  0 < internal_round_steps p z.
Proof.
  destruct z as [path guard].
  change (native_sample_value (internal_guard_native (internal_plan_residual p path)) guard = SHInternal u ->
    0 < internal_plan_steps p path + internal_guard_steps (internal_plan_residual p path)).
  intro Htarget. pose proof (internal_guard_progress Htarget). lia.
Qed.

Definition internal_target_budget fuel cost (target : stable_target tree head) : MF head :=
  if Nat.leb cost fuel then
    match target with
    | SHStable h => FORet h
    | SHInternal u => hit (fuel - cost) (observe u)
    end
  else FOZero.

Definition internal_guard_budget t fuel : MF head :=
  FOSample (native_sample_measure (internal_guard_native t)) (fun x =>
    internal_target_budget fuel (internal_guard_steps t)
      (native_sample_value (internal_guard_native t) x)).

Lemma internal_guard_hitting_approx t fuel :
  free_omega_qlift eq (hit fuel (observe t)) (internal_guard_budget t fuel).
Proof.
  unfold internal_guard_budget, internal_guard_native, internal_guard_steps.
  destruct (observe t); destruct fuel; unfold internal_target_budget; cbn;
    rewrite ?Nat.sub_0_r.
  all: try solve [apply free_omega_qlift_refl; intro h; reflexivity].
  all: apply FOQLMono with (T := fun x y => y = x).
  all: try solve [intros x y Hyx; symmetry; exact Hyx].
  all: apply FOQLSym, FOQLSampleRetL; [apply sem_ae_ret_iff|].
  all: apply free_omega_qlift_refl; intro h; reflexivity.
Qed.

Definition internal_round_budget {t} (p : @finite_internal_plan E MN R t) fuel : MF head :=
  FOSample (native_sample_measure (internal_plan_round_native p)) (fun z =>
    internal_target_budget fuel (internal_round_steps p z)
      (native_sample_value (internal_plan_round_native p) z)).

Lemma internal_target_budget_add fuel prefix cost target :
  internal_target_budget fuel (prefix + cost) target =
  if Nat.leb prefix fuel then internal_target_budget (fuel - prefix) cost target else FOZero.
Proof.
  unfold internal_target_budget.
  destruct (Nat.leb prefix fuel) eqn:Hp;
    destruct (Nat.leb (prefix + cost) fuel) eqn:Hall;
    destruct (Nat.leb cost (fuel - prefix)) eqn:Hc;
    try reflexivity.
  all: try (apply Nat.leb_le in Hp); try (apply Nat.leb_gt in Hp).
  all: try (apply Nat.leb_le in Hall); try (apply Nat.leb_gt in Hall).
  all: try (apply Nat.leb_le in Hc); try (apply Nat.leb_gt in Hc); try lia.
  replace (fuel - (prefix + cost)) with (fuel - prefix - cost) by lia.
  reflexivity.
Qed.

Lemma internal_guard_budget_prefix t fuel prefix :
  free_omega_qlift eq
    (if Nat.leb prefix fuel then hit (fuel - prefix) (observe t) else FOZero)
    (FOSample (native_sample_measure (internal_guard_native t)) (fun x =>
      internal_target_budget fuel (prefix + internal_guard_steps t)
        (native_sample_value (internal_guard_native t) x))).
Proof.
  destruct (Nat.leb prefix fuel) eqn:Hprefix.
  - eapply FOQLComp with (T := eq) (U := eq).
    + apply internal_guard_hitting_approx.
    + unfold internal_guard_budget. eapply FOQLSample with (T := eq).
      * apply sem_lift_refl. intro x. reflexivity.
      * intros x y ->. rewrite internal_target_budget_add, Hprefix.
        apply free_omega_qlift_refl. intro h. reflexivity.
    + intros x z [y [-> ->]]. reflexivity.
  - eapply FOQLComp with (T := eq) (U := eq)
      (mid := FOSample (native_sample_measure (internal_guard_native t)) (fun _ => FOZero)).
    + apply FOQLMono with (T := fun x y => y = x).
      * apply FOQLSym, FOQLSampleZero.
      * intros x y Hyx. symmetry. exact Hyx.
    + eapply FOQLSample with (T := eq).
      * apply sem_lift_refl. intro x. reflexivity.
      * intros x y ->. rewrite internal_target_budget_add, Hprefix.
        apply free_omega_qlift_refl. intro h. reflexivity.
    + intros x z [y [-> ->]]. reflexivity.
Qed.

End RoundCosts.

Arguments internal_round_steps {E MN NI R t} p _.

Section RoundAdequacy.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI} {R : Type}.
Local Notation head := (stable_head E MN R).
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation hit := (@ptree_hitting_approx E MN MF FI FreeOmegaMixedMeasure
  FreeOmegaObservableSemanticOmega R).

(** The COMPLETE round, including its guard, has exactly the primitive
    hitting law with its measured internal cost.  Subprobability loss and
    nonuniform branch depths are both preserved. *)
Theorem internal_round_hitting_approx t (p : @finite_internal_plan E MN R t) fuel :
  free_omega_qlift eq (hit fuel (observe t)) (internal_round_budget p fuel).
Proof.
  eapply FOQLComp with (T := eq) (U := eq); [apply internal_plan_hitting_approx| |].
  - eapply FOQLComp with (T := eq) (U := eq)
      (mid := FOSample (internal_plan_measure p) (fun path =>
        FOSample (native_sample_measure (internal_guard_native (internal_plan_residual p path)))
          (fun x => internal_target_budget fuel
            (internal_plan_steps p path + internal_guard_steps (internal_plan_residual p path))
            (native_sample_value (internal_guard_native (internal_plan_residual p path)) x)))).
    + unfold internal_plan_budget. eapply FOQLSample with (T := eq).
      * apply sem_lift_refl. intro path. reflexivity.
      * intros x y ->. exact (@internal_guard_budget_prefix E MN NI NC NO ND R
          (internal_plan_residual p y) fuel (internal_plan_steps p y)).
    + unfold internal_round_budget, internal_round_steps, internal_plan_round_native,
        free_omega_native_bind, internal_plan_native. cbn.
      exact (@free_omega_sample_sigma MN NI NC NO ND NBAE
        (internal_plan_path p)
        (fun path => native_sample_type (internal_guard_native (internal_plan_residual p path)))
        head (internal_plan_measure p)
        (fun path => native_sample_measure (internal_guard_native (internal_plan_residual p path)))
        (fun path x => internal_target_budget fuel
          (internal_plan_steps p path + internal_guard_steps (internal_plan_residual p path))
          (native_sample_value (internal_guard_native (internal_plan_residual p path)) x))).
    + intros x z [y [-> ->]]. reflexivity.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

(** Monotonicity is proved on the fixed round sample space, not by
    transporting raw approximation through quotient equality. *)
Lemma internal_round_budget_mono t (p : @finite_internal_plan E MN R t) n m :
  n <= m -> free_omega_approx eq (internal_round_budget p n) (internal_round_budget p m).
Proof.
  intro Hnm. unfold internal_round_budget, internal_target_budget.
  eapply FOApproxSample with (S := eq).
  - apply sem_lift_refl. intro z. reflexivity.
  - intros x y ->.
    destruct (Nat.leb (internal_round_steps p y) n) eqn:Hn;
      destruct (Nat.leb (internal_round_steps p y) m) eqn:Hm.
    + destruct (native_sample_value (internal_plan_round_native p) y).
      * apply FOApproxRet. reflexivity.
      * apply (@PTreeKernel.ptree_hitting_mono E MN MF FI
          FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
          FreeOmegaObservableSemanticMeasureOrderLaws R). lia.
    + apply Nat.leb_le in Hn. apply Nat.leb_gt in Hm. lia.
    + apply FOApproxZero.
    + apply FOApproxZero.
Qed.

Theorem internal_round_stable_hitting t (p : @finite_internal_plan E MN R t) out :
  @ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R (observe t) out ->
  free_omega_qlift eq out (FOLub (fun n => internal_round_budget p n)).
Proof.
  intro Hhit. eapply FOQLComp with (T := eq) (U := eq); [exact Hhit| |].
  - apply FOQLLub. intro n. apply internal_round_hitting_approx.
  - intros x z [y [-> ->]]. reflexivity.
Qed.
End RoundAdequacy.
