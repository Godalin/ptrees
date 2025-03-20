From ITree Require Import Basics.

From PTree.Core Require Import PTreeDefinitionFin.
From PTree.Prob Require Import FinSupp.



Section Sample.

Variable A : Type.

Variant sampleE : Type -> Type :=
| Sample : finSupp A -> sampleE A.

Definition h_sample {E} : sampleE ~> ptree E :=
  fun _ e =>
    match e with
    | Sample μ => meas μ
    end.



End Sample.
