(** Case role: supporting example.
    Reading entry: mathcomp_retry; mathcomp_nested_retry.
    Scope: Safe native syntax; direct frontier validation lives in the existing Gate M client.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDIES.md. *)
(** Safe syntax for MathComp acceptance. No recursive frontier is
    instantiated here; only its client in Gate M relaxes universe checking. *)
From Coq Require Import Utf8.

From mathcomp Require Import reals.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Backend.MathComp Require Import Kernel.
Set Implicit Arguments.

CoFixpoint mathcomp_retry {E A} (R : realType)
    (coin : MathCompKernelMeasure R bool) (value : A) :
    ptree E (MathCompKernelMeasure R) A :=
  Prob coin (λ b, if b then Ret value else Tau (mathcomp_retry coin value)).

Lemma mathcomp_retry_observe {E A} (R : realType)
    (coin : MathCompKernelMeasure R bool) (value : A) :
  observe (@mathcomp_retry E A R coin value) =
    ProbF coin (λ b, if b then Ret value else Tau (mathcomp_retry coin value)).
Proof. reflexivity. Qed.

Definition mathcomp_nested_retry {E A} (R : realType)
    (coin : MathCompKernelMeasure R bool) (value : A) :
    ptree E (MathCompKernelMeasure R) A :=
  PTree.bind (mathcomp_retry coin tt) (λ _, mathcomp_retry coin value).
