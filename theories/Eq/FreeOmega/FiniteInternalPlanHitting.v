Set Universe Polymorphism.
From Coq Require Import Arith.PeanoNat Lia.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure FreeOmegaNative.
From PTree.Eq Require Import FiniteInternalPlan UnifiedFrontier PrimitiveStableHitting PTreeKernel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Completed paths do not in general have the mass of earlier state
    prefixes: a later subprobability sample can kill a path.  Stable hitting
    has a more precise decomposition.  Paths longer than the observation
    budget contribute zero; other paths spend their ACTUAL length before
    continuing from the residual.  Fuel here is a semantic observation
    budget, not a bound on plans or a program-equivalence index. *)
Section PlanHitting.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI} {R : Type}.
Local Notation tree := (ptree E MN R).
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation hit := (@ptree_hitting_approx E MN MF FI FreeOmegaMixedMeasure
  FreeOmegaObservableSemanticOmega R).

Definition internal_plan_budget {t} (p : @finite_internal_plan E MN R t) fuel :=
  FOSample (internal_plan_measure p) (fun z =>
    if Nat.leb (internal_plan_steps p z) fuel then
      hit (fuel - internal_plan_steps p z) (observe (internal_plan_residual p z))
    else FOZero).

Theorem internal_plan_hitting_approx t (p : @finite_internal_plan E MN R t) fuel :
  free_omega_qlift eq (hit fuel (observe t)) (internal_plan_budget p fuel).
Proof.
  induction p as [t|t next IH|X mu k next IH] in fuel |- *.
  - unfold internal_plan_budget. cbn [internal_plan_measure internal_plan_steps internal_plan_residual].
    rewrite Nat.sub_0_r.
    apply FOQLMono with (T := fun x y => y = x).
    + apply FOQLSym, FOQLSampleRetL.
      * apply sem_ae_ret_iff.
      * apply free_omega_qlift_refl. intro h. reflexivity.
    + intros x y Hyx. symmetry. exact Hyx.
  - destruct fuel as [|fuel].
    + change (free_omega_qlift (@eq (stable_head E MN R)) FOZero
        (FOSample (internal_plan_measure next) (fun _ => FOZero))).
      apply FOQLMono with (T := fun x y => y = x).
      * apply FOQLSym, FOQLSampleZero.
      * intros x y Hyx. symmetry. exact Hyx.
    + change (free_omega_qlift eq (hit fuel (observe t)) (internal_plan_budget next fuel)).
      apply IH.
  - destruct fuel as [|fuel].
    + change (free_omega_qlift (@eq (stable_head E MN R)) (FOSample mu (fun _ => FOZero))
        (FOSample (internal_plan_measure (FIPProb mu next)) (fun _ => FOZero))).
      eapply FOQLComp with (T := eq) (U := eq) (mid := FOZero).
      * apply FOQLSampleZero.
      * apply FOQLMono with (T := fun x y => y = x).
        -- apply FOQLSym, FOQLSampleZero.
        -- intros x y Hyx. symmetry. exact Hyx.
      * intros x z [y [-> ->]]. reflexivity.
    + change (free_omega_qlift eq
        (FOSample mu (fun x => hit fuel (observe (k x))))
        (internal_plan_budget (FIPProb mu next) (S fuel))).
      eapply FOQLComp with (T := eq) (U := eq)
        (mid := FOSample mu (fun x => internal_plan_budget (next x) fuel)).
      * eapply FOQLSample with (T := eq).
        -- apply sem_lift_refl. intro x. reflexivity.
        -- intros x y ->. apply IH.
      * unfold internal_plan_budget. cbn [internal_plan_measure internal_plan_steps internal_plan_residual].
        exact (@free_omega_sample_sigma MN NI NC NO ND NBAE X
          (fun x => internal_plan_path (next x)) (stable_head E MN R) mu
          (fun x => internal_plan_measure (next x))
          (fun x z => if Nat.leb (internal_plan_steps (next x) z) fuel then
            hit (fuel - internal_plan_steps (next x) z)
              (observe (internal_plan_residual (next x) z)) else FOZero)).
      * intros x z [y [-> ->]]. reflexivity.
Qed.

(** A raw increasing chain on the SAME native sample space.  This does
    not transport raw order through the quotient equality proved above. *)
Lemma internal_plan_budget_mono t (p : @finite_internal_plan E MN R t) n m :
  n <= m -> free_omega_approx eq (internal_plan_budget p n) (internal_plan_budget p m).
Proof.
  intro Hnm. unfold internal_plan_budget.
  eapply FOApproxSample with (S := eq).
  - apply sem_lift_refl. intro z. reflexivity.
  - intros x y ->.
    destruct (Nat.leb (internal_plan_steps p y) n) eqn:Hn;
      destruct (Nat.leb (internal_plan_steps p y) m) eqn:Hm.
    + apply (@PTreeKernel.ptree_hitting_mono E MN MF FI
        FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
        FreeOmegaObservableSemanticMeasureOrderLaws R). lia.
    + apply Nat.leb_le in Hn. apply Nat.leb_gt in Hm. lia.
    + apply FOApproxZero.
    + apply FOApproxZero.
Qed.

Theorem internal_plan_stable_hitting t (p : @finite_internal_plan E MN R t) out :
  @ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R (observe t) out ->
  free_omega_qlift eq out (FOLub (fun n => internal_plan_budget p n)).
Proof.
  intro Hhit. eapply FOQLComp with (T := eq) (U := eq); [exact Hhit| |].
  - apply FOQLLub. intro n. apply internal_plan_hitting_approx.
  - intros x z [y [-> ->]]. reflexivity.
Qed.
End PlanHitting.
