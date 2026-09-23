(** Arbitrary weak source equivalence survives eliminating standard State.
    Final states are compared by equality, results by the supplied relation.
    The state machine reuses generic relational hitting and acceleration
    mathematics; no state-preservation capability is postulated. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder RelationalClosure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel
  PEutt StableHittingRelation.
From PTree.Interp Require Import State StateMachine StateMachineScheduling.
Set Implicit Arguments.
Unset Strict Implicit.

Section StatePreservation.
Context {S : Type} {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{BindOrd : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MixedOrd : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variable Hbind : relational_bind FI.
Variable Hzero : relational_zero FO.
Variable Hlimit : relational_lub FO.

Theorem run_state_peutt {A B} (RR : A -> B -> Prop)
    (t : ptree (stateE S +' E) MN A) (u : ptree (stateE S +' E) MN B) s :
  @peutt (stateE S +' E) MN MF FI FC MX FO A B RR t u ->
  @peutt E MN MF FI FC MX FO (S*A) (S*B) (state_result_rel RR)
    (run_state t s) (run_state u s).
Proof.
  intro Htu. eapply peutt_coinduction with (sim := state_bisim_candidate (MF := MF) RR).
  - intros v w [t0 [u0 [s0 [-> [-> Hsource]]]]].
    destruct (stable_hitting_exists (FI := FI) (FO := FO)
      state_machine_kernel (s0,t0)) as [mu Hmu].
    destruct (stable_hitting_exists (FI := FI) (FO := FO)
      state_machine_kernel (s0,u0)) as [nu Hnu].
    eapply stable_hitting_match_of_hitting_lift with (out1 := mu) (out2 := nu).
    + exact (state_machine_hitting_sound (Directed := Directed) Hmu).
    + exact (state_machine_hitting_sound (Directed := Directed) Hnu).
    + eapply (state_machine_complete_related Hbind (RR := RR) Hzero Hlimit)
        with (c := (s0,t0)) (d := (s0,u0)); try eassumption.
      split; [reflexivity|exact Hsource].
  - exists t,u,s. repeat split; try reflexivity. exact Htu.
Qed.

Lemma run_state_peutt_Proper {A} s :
  Proper (@peutt (stateE S +' E) MN MF FI FC MX FO A A eq ==>
          @peutt E MN MF FI FC MX FO (S*A) (S*A) (state_result_rel eq))
    (fun t => run_state t s).
Proof. intros t u Htu. exact (run_state_peutt s Htu). Qed.

(** Ordinary equality on the state/result pair is recovered extensionally;
    clients need no setoid instance for the conjunction-shaped relation. *)
Theorem run_state_peutt_eq {A}
    (t u : ptree (stateE S +' E) MN A) s :
  @peutt (stateE S +' E) MN MF FI FC MX FO A A eq t u ->
  @peutt E MN MF FI FC MX FO (S*A) (S*A) eq (run_state t s) (run_state u s).
Proof.
  intro H. eapply peutt_rel_mono; [|exact (run_state_peutt s H)].
  intros [s1 a1] [s2 a2] [Hs Ha]. cbn in Hs, Ha. subst. reflexivity.
Qed.

Lemma run_state_peutt_eq_Proper {A} :
  Proper (@peutt (stateE S +' E) MN MF FI FC MX FO A A eq ==> eq ==>
          @peutt E MN MF FI FC MX FO (S*A) (S*A) eq)
    (@run_state S E MN A).
Proof. intros t u Htu s s' ->. exact (run_state_peutt_eq s' Htu). Qed.
End StatePreservation.
