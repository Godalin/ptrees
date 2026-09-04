(** Probability well-formedness for the generic PTree syntax.

    [ptree] remains reusable over measure-like carriers, including future
    unnormalised weighting effects.  [probabilistic_ptree] is the precise
    contract that every native [Prob] node contains a subprobability measure.
    Intrinsically bounded carriers discharge this contract for every tree. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ProbabilityWellFormedness.
Context {E : Type -> Type} {M : Type -> Type}
  `{SI : SemanticMeasure M}
  `{SP : @SemanticSubprobability M SI}.
Context {R : Type}.

(** The pointwise continuation premise is intentionally stronger than AE.
    It is syntax-level well-formedness: even a currently zero-weight branch
    should not contain an invalid native probability node that could become
    reachable after program transformation.  The coinductive judgment is
    phrased over observations so its intrinsic-carrier proof needs only
    ordinary dependent elimination of [ptreeF], never elimination of the
    coinductive [ptree] itself. *)
CoInductive probabilistic_observation : ptree' E M R -> Prop :=
| ProbabilisticRet r : probabilistic_observation (RetF r)
| ProbabilisticTau t :
    probabilistic_observation (observe t) ->
    probabilistic_observation (TauF t)
| ProbabilisticVis X (e : E X) k :
    (forall x, probabilistic_observation (observe (k x))) ->
    probabilistic_observation (VisF e k)
| ProbabilisticProb X (mu : M X) k :
    sem_subprob mu ->
    (forall x, probabilistic_observation (observe (k x))) ->
    probabilistic_observation (ProbF mu k).

Definition probabilistic_ptree (t : ptree E M R) : Prop :=
  probabilistic_observation (observe t).

(** Every tree over an intrinsically bounded carrier is a probability tree.
    This is the theorem used by the canonical SubEnum and MathComp APIs, so
    their clients carry no recurring side conditions. *)
CoFixpoint probabilistic_observation_intrinsic
    `{SA : @SemanticSubprobabilityCarrierLaws M SI SP}
    (ot : ptree' E M R) : probabilistic_observation ot :=
  match ot with
  | RetF r => ProbabilisticRet r
  | TauF next =>
      ProbabilisticTau (probabilistic_observation_intrinsic (observe next))
  | @VisF _ _ _ _ _ e k =>
      ProbabilisticVis e
        (fun x => probabilistic_observation_intrinsic (observe (k x)))
  | @ProbF _ _ _ _ _ mu k =>
      ProbabilisticProb (mu := mu) (k := k) (sem_subprob_all mu)
        (fun x => probabilistic_observation_intrinsic (observe (k x)))
  end.

Definition probabilistic_ptree_intrinsic
    `{SA : @SemanticSubprobabilityCarrierLaws M SI SP}
    (t : ptree E M R) : probabilistic_ptree t :=
  probabilistic_observation_intrinsic (observe t).

End ProbabilityWellFormedness.
