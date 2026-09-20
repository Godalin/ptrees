Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import reals.
From mathcomp.reals_stdlib Require Import Rstruct.
From PTree.Prob Require Import TwoLevelMeasureSubEnum FreeOmegaNativeCoupling
  FreeOmegaNativeTransportSubEnum.

(** Instantiate the scalar audit with the standard real construction.
    No new semantic axiom is introduced by this instance. *)
#[global] Instance SubEnum_FreeOmegaNativeCouplingLaws :
  @FreeOmegaNativeCouplingLaws SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega.
Proof.
  constructor. intros A B p q R Hq.
  exact (subenum_native_quotient_coupling
    (@Real.Pack Rdefinitions.R (Real.on Rdefinitions.R)) Hq).
Qed.
