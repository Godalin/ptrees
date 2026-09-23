From PTree.Prob.Interface Require Import RelationalClosure.
From PTree.Eq Require Import Relation Shallow PStruct.
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

(** Elementary structural equations over any relationally continuous frontier.
    The four ordinary probability certificates are explicit; no PTree theorem
    is assumed and no global instance search is extended. *)
Section RelationalAlgebra.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}.
Variable Hbind : relational_bind FI.
Variable Hmixed : relational_mixed_bind NI FI MX.
Variable Hzero : relational_zero FO.
Variable Hlimit : relational_lub FO.

Theorem peutt_iter_unfold {I R}
    (step : I -> ptree E MN (I + R)) (i : I) :
  @peutt E MN MF FI FC MX FO R R eq
    (PTree.iter step i)
    (PTree.bind (step i) (fun lr =>
      match lr with
      | inl i' => Tau (PTree.iter step i')
      | inr r => Ret r
      end)).
Proof.
  apply (Relation.peutt_of_pstruct Hbind Hmixed Hzero Hlimit).
  apply observe_eq_pstruct.
  exact (observing_observe (unfold_aloop_ step i)).
Qed.

Theorem peutt_iter_structural {I R}
    (step1 step2 : I -> ptree E MN (I + R)) (i : I) :
  (forall j, pstruct eq (step1 j) (step2 j)) ->
  @peutt E MN MF FI FC MX FO R R eq
    (PTree.iter step1 i) (PTree.iter step2 i).
Proof.
  intro Hstep. apply (Relation.peutt_of_pstruct Hbind Hmixed Hzero Hlimit).
  apply pstruct_iter. exact Hstep.
Qed.

Theorem peutt_iter_rel
    {I1 I2 R1 R2}
    (SI : I1 -> I2 -> Prop) (RR : R1 -> R2 -> Prop)
    (f : I1 -> ptree E MN (I1 + R1))
    (g : I2 -> ptree E MN (I2 + R2))
    (Hstep : forall i1 i2, SI i1 i2 ->
      pstruct (pstruct_iter_sum_rel SI RR) (f i1) (g i2))
    i1 i2 :
  SI i1 i2 ->
  @peutt E MN MF FI FC MX FO R1 R2 RR
    (PTree.iter f i1) (PTree.iter g i2).
Proof.
  intro Hij. apply (Relation.peutt_of_pstruct Hbind Hmixed Hzero Hlimit).
  eapply pstruct_iter_rel; eauto.
Qed.

(** Parameter identity / naturality.  Post-processing the result of a loop
    is equivalent to pushing that Kleisli continuation into every successful
    step result.  The proof is structural and therefore supports visible
    events, probability, divergence, and unbounded iteration uniformly. *)
Theorem peutt_iter_natural {I A B}
    (step : I -> ptree E MN (I + A))
    (k : A -> ptree E MN B) (i : I) :
  @peutt E MN MF FI FC MX FO B B eq
    (PTree.bind (PTree.iter step i) k)
    (PTree.iter (pstruct_iter_natural_step step k) i).
Proof.
  apply (Relation.peutt_of_pstruct Hbind Hmixed Hzero Hlimit).
  apply pstruct_iter_natural.
Qed.

(** Double-dagger / codiagonal identity.  Nested retries at either sum layer
    are flattened into retries of one loop. *)
Theorem peutt_iter_codiagonal {I R}
    (step : I -> ptree E MN (I + (I + R))) (i : I) :
  @peutt E MN MF FI FC MX FO R R eq
    (PTree.iter (fun j => PTree.iter step j) i)
    (PTree.iter (pstruct_iter_codiagonal_flat_step step) i).
Proof.
  apply (Relation.peutt_of_pstruct Hbind Hmixed Hzero Hlimit).
  apply pstruct_iter_codiagonal.
Qed.

End RelationalAlgebra.
