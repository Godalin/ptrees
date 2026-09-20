(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import reals.
From mathcomp.reals_stdlib Require Import Rstruct.
From PTree.Prob.Backend Require Import TwoLevelMeasureSubEnum.
From PTree.Prob.FreeOmega Require Import FreeOmegaNativeCoupling.
From PTree.Prob.Backend.FreeOmega Require Import FreeOmegaNativeTransportSubEnum.

(** Instantiate the scalar audit with the standard real construction.
    No new semantic axiom is introduced by this instance. *)
#[global] Instance SubEnum_FreeOmegaNativeCouplingLaws :
  @FreeOmegaNativeCouplingLaws SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega.
Proof.
  constructor. intros A B p q R Hq.
  exact (subenum_native_quotient_coupling
    (@Real.Pack Rdefinitions.R (Real.on Rdefinitions.R)) Hq).
Qed.
