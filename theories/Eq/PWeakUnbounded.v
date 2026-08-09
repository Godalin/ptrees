Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift MeasureIteration.
From PTree.Eq Require Import PWeakAbstract.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Frontiers which may cross an unbounded, almost-surely terminating
    internal iteration.  The ordinary finite frontier remains available
    unchanged through [AUFFinite]. *)
Section UnboundedFrontier.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M}
  `{MO : @MeasureOmegaInterface M MI}.

Inductive aufrontier {R} :
    ptree' E M R -> M (aphead E M R) -> Prop :=
  | AUFFinite ot hs :
      apfrontier ot hs -> aufrontier ot hs
  | AUFIter {I : Type}
      (step : I -> ptree E M (I + R))
      (transition : I -> M (I + R)) i out :
      (forall j,
        apfrontier (observe (step j))
          (meas_bind (transition j)
            (fun next => meas_ret (APHRet next)))) ->
      meas_iter transition i out ->
      aufrontier (observe (PTree.iter step i))
        (meas_bind out (fun r => meas_ret (APHRet r))).

Lemma apfrontier_aufrontier {R} ot hs :
  @apfrontier E M MI R ot hs -> aufrontier ot hs.
Proof. apply AUFFinite. Qed.

(** Unbounded iteration is functional up to measure equality whenever the
    model's omega-limit is unique. *)
Lemma aufrontier_iter_unique
    `{OL : @MeasureOmegaLaws M MI MO}
    {I R} (transition : I -> M (I + R)) i out1 out2 :
  meas_iter transition i out1 ->
  meas_iter transition i out2 ->
  meas_eq out1 out2.
Proof. eapply meas_iter_unique. Qed.

End UnboundedFrontier.
