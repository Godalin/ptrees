(** Backend-independent client: heterogeneous sampled and return carriers,
    arbitrary return relation, and no totality assumption. *)
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Eq Require Import PrimitiveStableHitting PTreeKernel
  StableHittingRelation PEutt UpToProb.
Set Implicit Arguments.

Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.

Section Client.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{FI : SemanticMeasure MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MixedOmega : @MixedMeasureOmegaLaws MN MF NI FI MX FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Context {A B X Y Z : Type} (RR : A -> B -> Prop) (XR : X -> Y -> Prop)
  (mu : MN X) (nu : MN Y) (e : E Z)
  (k : Z -> X -> ptree E MN A) (h : Z -> Y -> ptree E MN B).
Hypothesis Hmu : sem_lift XR mu nu.
Hypothesis Hknown : forall z x y, XR x y -> peutt (MF := MF) RR (k z x) (h z y).

(** Exercise the known-equivalence summand inside sampling closure. The
    recursive summand is exercised by MixedHeadProtocol's Reply branch. *)
Example heterogeneous_known_sampling_context :
  peutt (MF := MF) RR
    (Vis e (fun z => Prob mu (k z))) (Vis e (fun z => Prob nu (h z))).
Proof.
  eapply (peutt_coinduction_upto_prob (NI := NI) (FI := FI) (FO := FO))
    with (sim := fun s1 s2 =>
      s1 = observe (Vis e (fun z => Prob mu (k z))) /\
      s2 = observe (Vis e (fun z => Prob nu (h z)))); try typeclasses eauto.
  - intros s1 s2 [-> ->]. apply stable_hitting_match_vis. intro z.
    eapply prob_upto_closure_sample; [exact Hmu|].
    intros x y Hxy. right. exact (@Hknown z x y Hxy).
  - split; reflexivity.
Qed.
End Client.
