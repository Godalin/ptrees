(** Arbitrary effect interpretation preserves whole-continuation bisimulation
    when the frontier model supplies relational increasing-limit closure.
    Internally returning handlers are handled by the two-phase machine;
    target bisimulation is never assumed before a target visible guard. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder RelationalClosure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel
  PEutt StableHittingRelation.
From PTree.Interp Require Import Kernel Preservation HandlerMachine HandlerMachineAcceleration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section UnrestrictedInterp.
Context {E F MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
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
Variable Hzero : relational_zero FO.
Variable Hlimit : relational_lub FO.
Variable handler : forall X, E X -> ptree F MN X.

Theorem handler_vis_fusion {A B} (RR : A -> B -> Prop) :
  interp_vis_fusion (MF := MF) RR handler.
Proof.
  intros X e k1 k2 Hk.
  destruct (stable_hitting_exists (FI := FI) (FO := FO)
    (handler_machine_kernel handler) (HandlerConfig (handler e) k1)) as [mu Hmu].
  destruct (stable_hitting_exists (FI := FI) (FO := FO)
    (handler_machine_kernel handler) (HandlerConfig (handler e) k2)) as [nu Hnu].
  eapply stable_hitting_match_of_hitting_lift with (out1 := mu) (out2 := nu).
  - apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
    exact (handler_machine_hitting_sound (Directed := Directed) Hmu).
  - apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
    exact (handler_machine_hitting_sound (Directed := Directed) Hnu).
  - eapply (handler_machine_complete_related
      (relational_bind_of_laws FB) (RR := RR) Hzero Hlimit)
      with (c := HandlerConfig (handler e) k1) (d := HandlerConfig (handler e) k2).
    + constructor. exact Hk.
    + exact Hmu.
    + exact Hnu.
Qed.

(** No syntactic guard, totality, termination, or handler-specific target
    preservation premise is required. The extra limit obligation belongs to
    the probability model, not to this theorem's conclusion. *)
Theorem peutt_interp {A B} (RR : A -> B -> Prop)
    (t : ptree E MN A) (u : ptree E MN B) :
  @peutt E MN MF FI FC MX FO A B RR t u ->
  @peutt F MN MF FI FC MX FO A B RR
    (PTree.interp handler t) (PTree.interp handler u).
Proof.
  apply (peutt_interp_of_vis_fusion
    (BindOrd := BindOrd) (MixedOrd := MixedOrd) (Directed := Directed)).
  apply handler_vis_fusion.
Qed.

Lemma peutt_interp_Proper {A} :
  Proper (@peutt E MN MF FI FC MX FO A A eq ==>
          @peutt F MN MF FI FC MX FO A A eq)
    (@PTree.interp E F MN handler A).
Proof. intros t u Htu. exact (peutt_interp Htu). Qed.
End UnrestrictedInterp.
