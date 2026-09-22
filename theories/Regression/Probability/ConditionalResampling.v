(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Arith Require Import PeanoNat.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg rat.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Coupling PTree.Prob.Backend.EnumQ.FrontierLift.
From PTree.Prob.Interface Require Import SemanticCoupling.
Require Import PTree.Prob.Backend.EnumQ.Disintegration.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.Disintegration.
From PTree.Eq Require Import PrimitiveStableHitting.
From PTree.Eq Require Import UnifiedFrontier.
From PTree.Eq.Internal.FreeOmega Require Import KernelCompletion.
From PTree.Eq.Internal.Backend Require Import KernelDisintegration.
From PTree.Regression.Backend Require Import EnumQMeasureRegression SubEnumQRegression.
From PTree.Regression.Probability Require Import EnumQDisintegration.

Set Implicit Arguments.
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).

(** A split-weight representation is a legitimate input marginal, not
    necessarily the literal list produced by mapping the witness joint. *)
Example split_coin_conditionals :
  exists joint conditional,
    semantic_coupling eq subenumQ_fair_split subenumQ_fair joint /\
    sem_eq (subenumQ_bind subenumQ_fair_split conditional) joint /\
    (forall a, sem_ae (conditional a) (fun p => fst p = a /\ a = snd p)) /\
    sem_ae subenumQ_fair_split (fun a => subenumQ_total (conditional a)).
Proof.
  apply subenumQ_coupling_disintegration.
  change (sem_eq subenumQ_fair_split subenumQ_fair).
  apply sem_eq_sym. exact subenumQ_fair_split_lift.
Qed.

(** Instantiate the kernel-level constructor at the actual high-universe
    paired states/heads needed by residual-compression proofs.  Native
    samples remain bool pairs; they never have to contain a PTree. *)
Section PairedTreeState.
Context {E : Type -> Type} {A B : Type}.
Local Notation Pair := (ptree E SubEnumQ A * ptree E SubEnumQ B)%type.
Local Notation Heads := (stable_head E SubEnumQ A * stable_head E SubEnumQ B)%type.
Variable joint : Pair -> SubEnumQ (bool * bool).
Variable marginal : Pair -> SubEnumQ bool.
Variable next : Pair -> bool * bool -> MF (stable_target Pair Heads).
Hypothesis Hgraph : forall s, sem_lift (fun p x => fst p = x) (joint s) (marginal s).

Example paired_tree_state_resampling :
  exists conditional : Pair -> bool -> SubEnumQ (bool * bool),
    forall s, free_omega_qlift eq
      (FOSample (marginal s) (fun a => FOSample (conditional s a) (next s)))
      (FOSample (joint s) (next s)).
Proof.
  destruct (@kernel_disintegration_exists Pair Heads bool bool joint marginal next Hgraph)
    as [conditional [Hreconstruct _]].
  exists conditional. intro s. apply free_omega_sample_disintegration.
  apply Hreconstruct.
Qed.
End PairedTreeState.

(** The continuation can return a higher-universe PTree.  Accidentally
    forcing semantic states into the native carrier would reject this. *)
Example tree_continuation_resampling {E : Type -> Type} {R : Type}
    (k : bool * bool -> MF (ptree E SubEnumQ R)) :
  free_omega_qlift eq
    (FOSample (subenumQ_first_marginal latent_coin)
      (fun a => FOSample (subenumQ_fiber_kernel latent_coin a) k))
    (FOSample latent_coin k).
Proof.
  apply free_omega_sample_disintegration.
  apply subenumQ_disintegration_reconstruct.
Qed.

(** The visible bit depends on the unbounded retry count, while the other
    bit determines whether to retry.  Thus the continuation uses BOTH pair
    components; replacing the latent bit by any fixed partner is invalid. *)
Definition retry_joint (n : nat) : SubEnumQ (bool * bool) :=
  subenumQ_bind subenumQ_fair (fun b => subenumQ_ret (Nat.even n,b)).

Definition retry_continue (n : nat) (p : bool * bool) : MF (stable_target nat bool) :=
  if snd p then FORet (SHStable (fst p)) else FORet (SHInternal (S n)).

Definition retry_direct_kernel n := FOSample (retry_joint n) (retry_continue n).
Definition retry_conditional_kernel n :=
  FOSample (subenumQ_ret (Nat.even n))
    (fun a => FOSample (subenumQ_fiber_kernel (retry_joint n) a) (retry_continue n)).

(** The first stage is genuinely deterministic.  The conditional second
    stage must retain the fair retry bit, rather than pick one partner. *)
Lemma retry_conditional_reconstruct n :
  sem_eq
    (subenumQ_bind (subenumQ_ret (Nat.even n)) (subenumQ_fiber_kernel (retry_joint n)))
    (retry_joint n).
Proof.
  eapply sem_eq_trans.
  - apply (@sem_bind_ret_l SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticMeasureBindLaws).
  - apply enumQ_meas_eq_of_eqenum. intros [a b].
    unfold retry_joint. destruct (Nat.even n), a, b; vm_compute; reflexivity.
Qed.

Example unbounded_retry_resampling n out1 out2 :
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega nat bool
    retry_direct_kernel n out1 ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega nat bool
    retry_conditional_kernel n out2 ->
  free_omega_qlift eq out1 out2.
Proof.
  intros Hleft Hright.
  eapply kernel_resampling_stable_hitting with (D := fun _ => True)
    (joint := retry_joint)
    (marginal := fun n => subenumQ_ret (Nat.even n))
    (conditional := fun n => subenumQ_fiber_kernel (retry_joint n))
    (continue := retry_continue).
  - intros q _. apply retry_conditional_reconstruct.
  - intros q _. eapply free_omega_ae_mono with (P := fun _ => True).
    + intros [o|q'] _; exact I.
    + apply (@sem_ae_true MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
  - exact I.
  - exact Hleft.
  - exact Hright.
Qed.
