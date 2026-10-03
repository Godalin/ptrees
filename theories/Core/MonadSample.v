(** A target operation for native sampling, not a probability-correctness
    certificate. [fold] accepts this algebra explicitly; [interp] selects
    the operation supplied by the target. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
Set Implicit Arguments.
Unset Strict Implicit.

(** Sampling result types need not fill the target's entire carrier universe:
    iteration may use larger machine states than native samples. *)
Class MonadSample@{sample native native_rep target target_rep}
    (MN : Type@{native} → Type@{native_rep})
    (T : Type@{target} → Type@{target_rep}) : Type := {
  msample : ∀ {X : Type@{sample}}, MN X → T X
}.

#[global] Instance MonadSample_ptree@{sample event event_rep native native_rep target_rep}
    {E : Type@{event} → Type@{event_rep}}
    {MN : Type@{native} → Type@{native_rep}} :
    MonadSample@{sample native native_rep _ target_rep} MN (ptree E MN).
Proof. constructor. intros X mu. exact (PTree.sample mu). Defined.
