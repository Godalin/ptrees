(** Generic owner and exact old FreeOmega specialization contracts. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import PEutt Algebra.
From PTree.Interp Require Import IterationUniform ExceptionFacts StatePreservation Unrestricted Guarded.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed.

Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.

(** No native measure instance, bind/order/omega laws, or relational-lub
    certificate is in scope. This is an explicit minimal client signature. *)
Section ShallowClient.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}.
Example generic_left_unit_minimal {A B} (a : A) (k : A -> ptree E MN B) :
  @peutt E MN MF FI FC MX FO B B eq (PTree.bind (Ret a) k) (k a).
Proof. apply peutt_bind_ret_l. Qed.

Example generic_prob_bind_minimal {X A B} (mu : MN X)
    (h : X -> ptree E MN A) (k : A -> ptree E MN B) :
  peutt (MF := MF) eq (PTree.bind (Prob mu h) k)
    (Prob mu (fun x => PTree.bind (h x) k)).
Proof. apply peutt_bind_prob. Qed.

Example generic_vis_map_minimal {X A B} (e : E X)
    (h : X -> ptree E MN A) (f : A -> B) :
  peutt (MF := MF) eq (PTree.fmap f (Vis e h))
    (Vis e (fun x => PTree.fmap f (h x))).
Proof. apply peutt_fmap_vis. Qed.

(** Equality rewrites both endpoints of a genuinely heterogeneous judgment,
    in a context with no bind/order/omega laws or backend registration. *)
Example generic_heterogeneous_endpoint_rewrite
    (t t' : ptree E MN bool) (u u' : ptree E MN nat)
    (Ht : peutt (MF := MF) eq t t') (Hu : peutt (MF := MF) eq u u')
    (H : peutt (MF := MF) (fun (b : bool) (n : nat) => n = if b then 1%nat else 0%nat) t' u') :
  peutt (MF := MF) (fun (b : bool) (n : nat) => n = if b then 1%nat else 0%nat) t u.
Proof. setoid_rewrite Ht. setoid_rewrite Hu. exact H. Qed.
End ShallowClient.

(** Exercise actual rewriting through constructor notations, not merely
    inference of their whole-node Proper declarations. No backend is loaded. *)
Section ConstructorClient.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MO : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.
Local Notation W := (peutt (MF := MF) eq).

Example generic_vis_context_rewrite {A X} (e : E X)
    (k h : X -> ptree E MN A) (H : pointwise_relation X W k h) :
  W (Vis e k) (Vis e h).
Proof. setoid_rewrite H. reflexivity. Qed.

Example generic_prob_context_rewrite {A X} (mu : MN X)
    (k h : X -> ptree E MN A) (H : pointwise_relation X W k h) :
  W (Prob mu k) (Prob mu h).
Proof. setoid_rewrite H. reflexivity. Qed.
End ConstructorClient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Return reflection is heterogeneous and independent of completion syntax.
    The extra separation requirements are explicit probability-level laws. *)
Section ReturnReflection.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}
  `{CA : @SemanticMeasureCouplingAELaws MF FI}
  `{D : @SemanticMeasureDiracAELaws MF FI}.
Example generic_heterogeneous_ret_iff {A B} (RR : A -> B -> Prop) a b :
  @peutt E MN MF FI FC MX FO A B RR (Ret a) (Ret b) <-> RR a b.
Proof. apply peutt_ret_iff. Qed.
End ReturnReflection.

Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Semantics.MDPCoincidence.mdp_state_peutt_trans_iff.

Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure
  PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.BindOrder
  PTree.Prob.FreeOmega.RelationalLimit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FreeOmegaClient.
Context {E MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI} `{NO : @SemanticOmega MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation W := (@peutt E MN MF FI FC FreeOmegaMixedMeasure FO).

Example free_omega_frontier_ae_lift : @SemanticMeasureAELiftLaws MF FI.
Proof. apply coupling_ae_implies_ae_lift. Qed.

Example free_omega_frontier_dirac_ae : @SemanticMeasureDiracAELaws MF FI.
Proof. apply free_omega_observable_dirac_ae_laws. Qed.

Example free_omega_sample_bind {X A} (mu : MN X) (k : X -> ptree E MN A) :
  W eq (PTree.bind (Prob mu (fun x => Ret x)) k) (Prob mu k).
Proof. apply peutt_sample_bind. Qed.

Example free_omega_sample_map `{NDirac : @SemanticMeasureDiracAELaws MN NI}
    `{NBindAE : @SemanticMeasureBindAEExactLaws MN NI}
    {X A} (mu : MN X) (f : X -> A) :
  W eq (Prob mu (fun x => Ret (f x)))
    (Prob (sem_bind mu (fun x => sem_ret (f x))) (fun a => Ret a)).
Proof. apply (peutt_sample_map (NI := NI)). Qed.
End FreeOmegaClient.

(** The real-weight native model assembles the same interpretation theorem,
    without a second completion or interpreter proof. *)
From mathcomp Require Import reals.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega.
Require Import PTree.Prob.FreeOmega.BindOrder.
Section RealInterpretation.
Variable R : realType.
Context {E F : Type -> Type} {A B : Type}.
Local Notation MN := (SubEnumR R).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumR_SemanticMeasure R) (NO := SubEnumR_SemanticOmega R)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnumR_SemanticMeasure R) (NO := SubEnumR_SemanticOmega R)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumR_SemanticMeasure R) (NO := SubEnumR_SemanticOmega R)).
Variable handler : forall X, E X -> ptree F MN X.
Variable RR : A -> B -> Prop.

Example real_guarded_interp
    (Hg : @Guarded.guarded_handler E F MN (FreeOmega MN) FI FreeOmegaMixedMeasure FO handler)
    (t : ptree E MN A) (u : ptree E MN B) :
  @peutt E MN (FreeOmega MN) FI FC FreeOmegaMixedMeasure FO A B RR t u ->
  @peutt F MN (FreeOmega MN) FI FC FreeOmegaMixedMeasure FO A B RR
    (PTree.interp handler t) (PTree.interp handler u).
Proof. apply Guarded.peutt_interp_guarded. exact Hg. Qed.
End RealInterpretation.
