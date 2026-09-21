(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
Require Import PTree.Prob.Backend.Common.RatSubTypes PTree.Prob.Backend.Enum.Representation PTree.Prob.Backend.Enum.FrontierLift PTree.Prob.Backend.SubEnum.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnum.FreeOmega.UpperExpectation PTree.Prob.Backend.SubEnum.FreeOmega.UpperContinuity.
From PTree.Regression.Backend Require Import FreeOmegaEscapingMass.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum RatSubTypes GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

(** A syntactically present, zero-weight branch deliberately decreases.
    The numeric sample/limit law must need monotonicity only almost
    everywhere, not on all syntactic samples. *)
Definition null_branch_node : SubEnum bool.
Proof.
  refine {| subenum_raw := (1,true) :: (0,false) :: nil |}.
  vm_compute. reflexivity.
Defined.

Definition null_branch_chain (b : bool) (n : nat) : FreeOmega SubEnum bool :=
  if b then FORet true else match n with O => FORet false | S _ => FOZero end.

Lemma null_branch_chain_ae_increasing :
  enum_ae (subenum_raw null_branch_node)
    (fun b => forall n, free_omega_approx eq
      (null_branch_chain b n) (null_branch_chain b (S n))).
Proof.
  intros p b Hin Hnz n. destruct Hin as [H|[H|H]]; [| |contradiction].
  - inversion H. subst. apply free_omega_approx_refl. intro x. reflexivity.
  - inversion H. subst. exfalso. apply Hnz. apply val_inj. reflexivity.
Qed.

Lemma null_branch_chain_not_everywhere_increasing :
  ~ (forall b n, free_omega_approx eq
    (null_branch_chain b n) (null_branch_chain b (S n))).
Proof.
  intro H. specialize (H false 0%nat).
  cbn [null_branch_chain] in H. inversion H.
Qed.

Section ScalarContinuityRegression.
Variable R : realType.
Local Notation upper := (free_omega_upper (R := R)).

Theorem null_branch_sample_limit (f : bool -> R)
    (Hf : forall b, 0 <= f b /\ f b <= 1) :
  upper (FOSample null_branch_node (fun b => FOLub (null_branch_chain b))) f =
  upper (FOLub (fun n => FOSample null_branch_node (fun b => null_branch_chain b n))) f.
Proof.
  apply free_omega_sample_lub_upper; [exact null_branch_chain_ae_increasing|exact Hf].
Qed.

Theorem null_branch_sample_mass :
  upper (FOSample null_branch_node (fun b => FOLub (null_branch_chain b))) (fun _ => 1) = 1.
Proof.
  cbn [free_omega_upper null_branch_node subenum_raw enum_real_expect null_branch_chain].
  rewrite ?rmorph1 ?rmorph0 mul1r mul0r !addr0.
  apply countable_upper_constant.
Qed.

(** The bind theorem allows malformed formal Lub nodes INSIDE each
    source term.  It requires exactly increasing outer source/kernel
    chains; no hidden totality, AST or hereditary well-formedness premise
    rules out the escaping source from the previous safety audit. *)
Theorem escaping_source_bind_limit (f : unit -> R)
    (Hf : forall x, 0 <= f x /\ f x <= 1) :
  upper (free_omega_bind (FOLub (fun _ => EscapingMass.escaping))
    (fun x => FOLub (EscapingMass.kernel x))) f =
  upper (FOLub (fun n => free_omega_bind EscapingMass.escaping
    (fun x => EscapingMass.kernel x n))) f.
Proof.
  apply free_omega_bind_lub_upper.
  - intro n. apply free_omega_approx_refl. intro x. reflexivity.
  - exact EscapingMass.kernel_increasing.
  - exact Hf.
Qed.
End ScalarContinuityRegression.
