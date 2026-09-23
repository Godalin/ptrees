(** Generic eventful iteration coinduction. The generator-closure premise
    is explicit: this is not arbitrary behavioral step congruence. No
    probability completion, native law, or no-event restriction is used. *)
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel PEutt StableHittingRelation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section EventfulBehavioralIterationClosure.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}.
Context {I1 I2 R1 R2 : Type}.
Variable step1 : I1 -> ptree E MN (I1 + R1).
Variable step2 : I2 -> ptree E MN (I2 + R2).
Variable SI : I1 -> I2 -> Prop.
Variable RR : R1 -> R2 -> Prop.

(** Native coinduction candidate for eventful behavioral fusion.  Unlike the
    eventless grid theorem, it does not erase visible heads: their
    continuations must re-enter this candidate. *)
Definition iter_eventful_bisim_candidate
    (s1 : ptree' E MN R1) (s2 : ptree' E MN R2) : Prop :=
  exists i1 i2,
    SI i1 i2 /\
    s1 = observe (PTree.iter step1 i1) /\
    s2 = observe (PTree.iter step2 i2).

(** Exact generator-level obligation for eventful behavioral iteration.
    This is deliberately independent of finite schedules and of the
    eventless complete-row construction. *)
Definition iter_eventful_generator_closed : Prop :=
  forall i1 i2, SI i1 i2 ->
    @stable_hitting_match MF
      FI
      FO
      (ptree' E MN R1) (ptree' E MN R2)
      (stable_head E MN R1) (stable_head E MN R2)
      (@ptree_primitive_kernel E MN MF
        FI
        MX R1)
      (@ptree_primitive_kernel E MN MF
        FI
        MX R2)
      (@ptree_stable_head_rel E MN R1 R2 RR)
      iter_eventful_bisim_candidate
      (observe (PTree.iter step1 i1))
      (observe (PTree.iter step2 i2)).

Theorem peutt_iter_eventful_of_generator_closed
    (Hclosed : iter_eventful_generator_closed) :
  forall i1 i2, SI i1 i2 ->
  @peutt E MN MF
    FI
    FC
    MX
    FO R1 R2 RR
    (PTree.iter step1 i1) (PTree.iter step2 i2).
Proof.
  intros i1 i2 Hij.
  eapply peutt_coinduction with
      (sim := iter_eventful_bisim_candidate).
  - intros s1 s2 [j1 [j2 [Hj [-> ->]]]]. exact (Hclosed j1 j2 Hj).
  - exists i1, i2. repeat split; try reflexivity. exact Hij.
Qed.

End EventfulBehavioralIterationClosure.
