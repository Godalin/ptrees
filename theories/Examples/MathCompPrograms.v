(** Safe syntax for direct MathComp acceptance. No recursive frontier is
    instantiated here; only its client in Gate M relaxes universe checking. *)
From mathcomp Require Import reals.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Backend.MathComp Require Import Kernel.
Set Implicit Arguments.

CoFixpoint mathcomp_retry {E A} (R : realType)
    (coin : MathCompKernelMeasure R bool) (value : A) :
    ptree E (MathCompKernelMeasure R) A :=
  Prob coin (fun b => if b then Ret value else Tau (mathcomp_retry coin value)).

Lemma mathcomp_retry_observe {E A} (R : realType)
    (coin : MathCompKernelMeasure R bool) (value : A) :
  observe (@mathcomp_retry E A R coin value) =
    ProbF coin (fun b => if b then Ret value else Tau (mathcomp_retry coin value)).
Proof. reflexivity. Qed.

Definition mathcomp_nested_retry {E A} (R : realType)
    (coin : MathCompKernelMeasure R bool) (value : A) :
    ptree E (MathCompKernelMeasure R) A :=
  PTree.bind (mathcomp_retry coin tt) (fun _ => mathcomp_retry coin value).
