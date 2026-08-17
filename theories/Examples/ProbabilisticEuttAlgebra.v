Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC TwoLevelMeasure TwoLevelMeasureEnum
  FreeOmegaMeasure MeasureIterationEnum.
From PTree.Eq Require Import OperationalProbabilisticPTS
  OperationalProbabilisticPTSFreeOmega ProbabilisticEutt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.

Variant algebraE : Type -> Type := .
Local Notation MF := (FreeOmega Enum).
Local Notation peutt :=
  (@probabilistic_eutt algebraE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface).

(** Regression: all three monad equations elaborate at the canonical
    FreeOmega endpoint. *)
Lemma canonical_monad_laws_regression {A B C}
    (a : A) (t : ptree algebraE Enum A)
    (k : A -> ptree algebraE Enum B)
    (h : B -> ptree algebraE Enum C) :
  peutt eq (PTree.bind (Ret a) k) (k a) /\
  peutt eq (PTree.bind t (fun x => Ret x)) t /\
  peutt eq
    (PTree.bind (PTree.bind t k) h)
    (PTree.bind t (fun x => PTree.bind (k x) h)).
Proof.
  repeat split.
  - apply free_probabilistic_eutt_bind_ret_l.
  - apply free_probabilistic_eutt_bind_ret_r.
  - apply free_probabilistic_eutt_bind_assoc.
Qed.

(** Regression: the bind [Proper] instance supports rewriting a canonical
    equivalence underneath a continuation. *)
Lemma canonical_bind_setoid_rewrite {A B}
    (t1 t2 : ptree algebraE Enum A)
    (k : A -> ptree algebraE Enum B) :
  peutt eq t1 t2 ->
  peutt eq (PTree.bind t1 k) (PTree.bind t2 k).
Proof.
  intro Ht. setoid_rewrite Ht. reflexivity.
Qed.
