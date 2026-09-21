(** Role: Canonical FreeOmega measure infrastructure. Depends on generic measures; not a concrete native backend or program equivalence. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed PTree.Prob.Interface.SemanticCoupling.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Native.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Optional realization capability, not a law of the base measure
    interface.  A quotient coupling of two finite/native presentations
    admits an actual joint on the original sample carriers.  This law
    mentions neither trees, stable hitting, nor behavioral equivalence.
    It is proved for SubEnum rather than assumed there.  In particular it
    must not be registered for arbitrary backends from core laws alone. *)
Class FreeOmegaNativeCouplingLaws {MN : Type -> Type}
    (NI : SemanticMeasure MN) (NO : @SemanticOmega MN NI) := {
  free_omega_native_coupling : forall {A B}
    (p : free_omega_native_presentation MN A)
    (q : free_omega_native_presentation MN B) (R : A -> B -> Prop),
    @free_omega_qlift MN NI NO A B R (free_omega_native p) (free_omega_native q) ->
    exists joint : MN (native_sample_type p * native_sample_type q)%type,
      @semantic_coupling MN NI _ _
        (fun x y => R (native_sample_value p x) (native_sample_value q y))
        (native_sample_measure p) (native_sample_measure q) joint
}.

(** The same capability subsumes native lifting realization.  The proof
    embeds one primitive coupling in the quotient, then uses the identity
    decoders; there is no independent choice/gluing assumption here. *)
Lemma free_omega_native_node_coupling {MN : Type -> Type}
    `{NI : SemanticMeasure MN} `{NO : @SemanticOmega MN NI}
    `{NJ : @FreeOmegaNativeCouplingLaws MN NI NO}
    {X Y} (R : X -> Y -> Prop) (mu : MN X) (nu : MN Y) :
  sem_lift R mu nu -> exists joint, semantic_coupling R mu nu joint.
Proof.
  intro Hlift.
  pose (p := {| native_sample_type := X; native_sample_measure := mu;
                native_sample_value := fun x => x |}).
  pose (q := {| native_sample_type := Y; native_sample_measure := nu;
                native_sample_value := fun y => y |}).
  apply (free_omega_native_coupling (p := p) (q := q) (R := R)).
  eapply FOQLSample; [exact Hlift|].
  intros x y Hxy. apply FOQLStructural, FOLRet. exact Hxy.
Qed.
