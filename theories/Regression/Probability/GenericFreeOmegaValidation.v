(** Native-parametric external validation contracts. Mainline reasoning must
    not acquire a dependence on this external model. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Domain Require Import Expectation.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega.Validation Require Import Expectation.

Fail Check PTree.Prob.Backend.SubEnum.Measure.SubEnum.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.
Fail Check PTree.Prob.FreeOmega.Observation.free_omega_denotes.
Fail Check PTree.Core.PTreeDefinition.ptree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

(** A genuinely different native interpretation: no finite enumeration,
    rational weights, native omega structure or native coupling is needed. *)
Definition option_model (R : realType) X (mu : option X) : OmegaVal R X :=
  match mu with None => oval_bottom R | Some x => oval_ret R x end.
Example option_sample_denotes (R : realType) :
  free_omega_model_denotes (fun X => @option_model R X)
    (FOSample (Some true) (fun b => FORet (negb b))) (oval_ret R false).
Proof. intros f Hf; reflexivity. Qed.

From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Backend.SubEnum Require Import Measure Domain.
From PTree.Prob.Backend.SubEnum.FreeOmega Require Import Admissibility GenericValidation.
From PTree.Regression.Fixtures Require Import FreeOmegaSamples.
From PTree.Regression.Probability Require Import FreeOmegaDomain.

Section SubEnumContracts.
Variable R : realType.
Local Notation native := (fun X => @subenum_domain R X).

Example generic_null_bad_sample :
  free_omega_modelable native (FOSample null_weight_node nullable_kernel).
Proof.
  apply (modelable_sample_ae (NI := SubEnum_SemanticMeasure)); first exact (@subenum_native_model_ae R).
  eapply sem_ae_mono; [|exact (nullable_kernel_ae R)].
  intros x Hx; exact (proj2 (subenum_modelable_iff_admissible R _) Hx).
Qed.

Example generic_null_bad_bind :
  free_omega_modelable native
    (free_omega_bind (FOSample null_weight_node (fun b => FORet b)) nullable_kernel).
Proof.
  apply (modelable_bind_ae (NI := SubEnum_SemanticMeasure)); first exact (@subenum_native_model_ae R).
  - apply modelable_sample=> b; exact: modelable_ret.
  - eapply FOAESample; [exact (nullable_kernel_ae R)|].
    intros b Hb; apply FOAERet; exact (proj2 (subenum_modelable_iff_admissible R _) Hb).
Qed.

Example generic_rejects_raw_alternation : ~ free_omega_modelable native alternating_bool.
Proof. intro H; apply (@alternating_bool_not_admissible R); exact (proj1 (subenum_modelable_iff_admissible R _) H). Qed.

Example generic_geometric_modelable : free_omega_modelable native geometric.
Proof.
  apply (modelable_lub_approx (NI := SubEnum_SemanticMeasure)); first exact (@subenum_native_model_lift R).
  - intro n; generalize O as start; induction n=> start; first apply modelable_zero.
    cbn [geometric_prefix]; apply modelable_sample.
    intro b; destruct b; [apply modelable_ret|apply IHn].
  - intro n; exact: geometric_prefix_increasing.
Qed.

Example generic_geometric_agrees :
  oval_eq (free_omega_model generic_geometric_modelable) (free_omega_domain (geometric_valid R)).
Proof. exact: subenum_generic_domain_agrees. Qed.

Example generic_validity_proof_independent (H K : free_omega_modelable native geometric) :
  oval_eq (free_omega_model H) (free_omega_model K).
Proof. intros f Hf; reflexivity. Qed.
End SubEnumContracts.

Section HighUniverse.
Universe u.
Variable R : realType.
Example generic_high_result (A : Type@{u}) :
  free_omega_modelable (fun X => @subenum_domain R X)
    (@FORet SubEnum Type@{u} A).
Proof. exact: modelable_ret. Qed.
End HighUniverse.
