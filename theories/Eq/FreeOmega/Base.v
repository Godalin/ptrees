(** Role: FreeOmega specialization of primitive hitting monotonicity.
    Translation approximants and preservation live in Interp/FreeOmega/Translate;
    no concrete native backend is selected here. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq.Arith Require Import PeanoNat.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Eq Require Import PTreeKernel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FreeOmegaBase.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}.

Local Notation MF := (FreeOmega MN).

Lemma ptree_hitting_mono {R} (ot : ptree' E MN R) n m :
  Peano.le n m ->
  free_omega_approx eq
    (ptree_hitting_approx (MF := MF) n ot)
    (ptree_hitting_approx (MF := MF) m ot).
Proof.
  apply (ptree_hitting_mono
    (FI := FreeOmegaObservableSemanticMeasure)
    (FO := FreeOmegaObservableSemanticOmega)
    (MX := FreeOmegaMixedMeasure)).
Qed.

(** Explicit observable-interface endpoint for limit-rule premises. *)
Lemma ptree_observable_hitting_increasing {F R} (ot : ptree' F MN R) n :
  free_omega_approx eq
    (@ptree_hitting_approx F MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega R n ot)
    (@ptree_hitting_approx F MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega R (S n) ot).
Proof.
  exact (@PTreeKernel.ptree_hitting_mono F MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
    FreeOmegaObservableSemanticMeasureOrderLaws R ot n (S n)
    (Nat.le_succ_diag_r n)).
Qed.

End FreeOmegaBase.
