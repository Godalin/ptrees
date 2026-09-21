(** Safe same-carrier probability infrastructure: MN = MF at the native
    MathComp carrier universe. This is NOT yet a recursive PTree self-model.
    In particular, no relational-bind or omega-existence axiom is introduced.
    Universe checking stays enabled throughout. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals boolp classical_sets.
From mathcomp.analysis Require Import measure ereal.
From mathcomp Require Import numfun lebesgue_integral.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section SelfModel.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).

#[global] Instance MathCompSelfMixedMeasure : MixedMeasure M M := {
  mixed_bind := @mathcomp_kernel_bind R
}.

#[global] Instance MathCompSelfMixedMeasureUnitLaws :
  @MixedMeasureUnitLaws M M NI NI MathCompSelfMixedMeasure.
Proof.
  constructor; intros A B x k; cbn [mixed_bind sem_ret sem_lift].
  eapply mathcomp_kernel_lift_proper_l.
  - apply mathcomp_kernel_eq_sym; exact: mathcomp_kernel_bind_ret_l.
  - apply mathcomp_kernel_lift_refl; intro y; reflexivity.
Qed.

#[global] Instance MathCompSelfMixedMeasureNodeBindLaws :
  @MixedMeasureNodeBindLaws M M NI NI MathCompSelfMixedMeasure.
Proof.
  constructor; intros A B C mu h k; cbn [mixed_bind sem_bind sem_lift].
  eapply mathcomp_kernel_lift_proper_l.
  - exact: mathcomp_kernel_bind_assoc.
  - apply mathcomp_kernel_lift_refl; intro y; reflexivity.
Qed.

#[global] Instance MathCompSelfTotalProperLaws : @SemanticTotalProperLaws M NI NO.
Proof. constructor; exact (@mathcomp_kernel_total_proper R). Qed.

Lemma mathcomp_self_zero_returned {A} (U : set (mc_carrier A)) :
  ~ U MCBottom -> mathcomp_kernel_root (@mathcomp_kernel_zero R A) U = 0.
Proof.
  intro H; rewrite /mathcomp_kernel_zero /mathcomp_kernel_root
    /mathcomp_source_kernel /mathcomp_source_measure /mathcomp_bottom_measure /dirac.
  change ((indic U MCBottom : R)%:E = 0).
  rewrite indicE.
  have Hnot : (MCBottom \in U) = false by apply/asboolPn.
  by rewrite Hnot.
Qed.
Lemma mathcomp_self_le_refl {A} (mu : M A) : mathcomp_node_le mu mu.
Proof. intros U mU Hbot; exact: lexx. Qed.
Lemma mathcomp_self_le_trans {A} (mu nu xi : M A) :
  mathcomp_node_le mu nu -> mathcomp_node_le nu xi -> mathcomp_node_le mu xi.
Proof. intros H1 H2 U mU Hb; exact: le_trans (H1 U mU Hb) (H2 U mU Hb). Qed.
Lemma mathcomp_self_zero_le {A} (mu : M A) : mathcomp_node_le (mathcomp_kernel_zero R) mu.
Proof. intros U mU Hbot; rewrite (mathcomp_self_zero_returned Hbot); exact: measure_ge0. Qed.

Lemma mathcomp_self_lub_constant {A} (mu : M A) : mathcomp_kernel_lub (fun _ => mu) mu.
Proof.
  intros U mU Hbot; symmetry.
  have He : [set mathcomp_kernel_root mu U | n in [set: nat]] = [set mathcomp_kernel_root mu U].
  { apply/seteqP; split.
    - intros z [n _ <-]; reflexivity.
    - intros z ->; exists O; [exact I|reflexivity]. }
  rewrite He; exact: ereal_sup1.
Qed.

Lemma mathcomp_self_prefix_sup {A} (c : nat -> M A) (U : set (mc_carrier A)) :
  ~ U MCBottom ->
  ereal_sup [set mathcomp_kernel_root (c n) U | n in [set: nat]] =
  ereal_sup [set mathcomp_kernel_root ((@sem_zero_prefix M NI NO A c) n) U | n in [set: nat]].
Proof.
  intro Hbot; apply/eqP; rewrite eq_le; apply/andP; split; apply ub_ereal_sup.
  - intros z [n _ <-]; apply ereal_sup_ge.
    exists (mathcomp_kernel_root (c n) U); last exact: lexx.
    exists (S n); [exact I|reflexivity].
  - intros z [[|n] _ <-].
    + change (mathcomp_kernel_root (@mathcomp_kernel_zero R A) U <=
        ereal_sup [set mathcomp_kernel_root (c n) U | n in [set: nat]]).
      rewrite (mathcomp_self_zero_returned Hbot); apply ereal_sup_ge.
      exists (mathcomp_kernel_root (c O) U); last exact: measure_ge0.
      exists O; [exact I|reflexivity].
    + apply ereal_sup_ge; exists (mathcomp_kernel_root (c n) U); last exact: lexx.
      exists n; [exact I|reflexivity].
Qed.

#[global] Instance MathCompSelfCofinalityLaws : @SemanticOmegaCofinalityLaws M NI NO.
Proof.
  constructor.
  - intros A c out; split; intros H U mU Hbot.
    + rewrite -(mathcomp_self_prefix_sup c Hbot); exact (H U mU Hbot).
    + rewrite (mathcomp_self_prefix_sup c Hbot); exact (H U mU Hbot).
  - exact @mathcomp_self_lub_constant.
Qed.

(** Bind in the continuation direction is monotone by ordinary integration.
    The source direction needs comparison of measures, not this lemma. *)
Lemma mathcomp_self_bind_le_k {A B} (mu : M A) (k h : A -> M B) :
  (forall x, mathcomp_node_le (k x) (h x)) ->
  mathcomp_node_le (mathcomp_kernel_bind mu k) (mathcomp_kernel_bind mu h).
Proof.
  intros H U mU Hbot; rewrite !mathcomp_kernel_root_bind.
  apply ge0_le_integral; try exact: measurableT.
  - intros x _; exact: measure_ge0.
  - exact: measurable_mathcomp_kernel_extend mU.
  - intros x _; exact: measure_ge0.
  - exact: measurable_mathcomp_kernel_extend mU.
  - intros [|x] _; [exact: lexx|exact (H x U mU Hbot)].
Qed.
End SelfModel.
