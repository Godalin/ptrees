(** Probability well-formedness for the generic PTree syntax.

    [ptree] remains reusable over measure-like carriers, including future
    unnormalised weighting effects.  [probabilistic_ptree] is the precise
    contract that every native [Prob] node contains a subprobability measure.
    Intrinsically bounded carriers discharge this contract for every tree. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

From Coq Require Import Program.Equality.
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

(** The syntax constructors preserve probability well-formedness.  These
    lemmas are useful for carriers such as raw [Enum], where validity is a
    genuine predicate rather than an intrinsic property of every measure. *)
Definition probabilistic_ptree_ret (r : R) :
    probabilistic_ptree (PTree.ret r) :=
  ProbabilisticRet r.

Definition probabilistic_ptree_tau (t : ptree E M R)
    (Ht : probabilistic_ptree t) :
    probabilistic_ptree (Tau t) :=
  ProbabilisticTau Ht.

Definition probabilistic_ptree_vis {X} (e : E X)
    (k : X -> ptree E M R)
    (Hk : forall x, probabilistic_ptree (k x)) :
    probabilistic_ptree (Vis e k) :=
  ProbabilisticVis e Hk.

Definition probabilistic_ptree_prob {X} (mu : M X)
    (k : X -> ptree E M R)
    (Hmu : sem_subprob mu)
    (Hk : forall x, probabilistic_ptree (k x)) :
    probabilistic_ptree (Prob mu k) :=
  ProbabilisticProb Hmu Hk.

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

Section ProbabilityWellFormednessCombinators.
Context {E : Type -> Type} {M : Type -> Type}
  `{SI : SemanticMeasure M}
  `{SP : @SemanticSubprobability M SI}.

Local Lemma observe_bind_probability {T U}
    (t : ptree E M T) (k : T -> ptree E M U) :
  observe (PTree.bind t k) =
  observe (match observe t with
    | RetF r => k r
    | TauF t0 => Tau (PTree.bind t0 k)
    | VisF _ e ke => Vis e (fun x => PTree.bind (ke x) k)
    | ProbF _ mu ke => Prob mu (fun x => PTree.bind (ke x) k)
    end).
Proof. reflexivity. Qed.

(** Syntactic bind retains every existing node measure and only transforms
    its continuation.  Consequently this closure theorem needs no
    [SemanticSubprobabilityLaws] assumption about measure-level bind. *)
CoFixpoint probabilistic_ptree_bind {T U}
    (t : ptree E M T) (k : T -> ptree E M U)
    (Ht : probabilistic_ptree t)
    (Hk : forall x, probabilistic_ptree (k x)) :
    probabilistic_ptree (PTree.bind t k).
Proof.
  unfold probabilistic_ptree in *.
  rewrite observe_bind_probability.
  destruct (observe t) eqn:Hot.
  - cbn. dependent destruction Ht. apply Hk.
  - cbn. dependent destruction Ht. constructor.
    eapply probabilistic_ptree_bind; eauto.
  - cbn. dependent destruction Ht. constructor. intro x.
    eapply probabilistic_ptree_bind; eauto.
  - cbn. dependent destruction Ht. constructor.
    + assumption.
    + intro x. eapply probabilistic_ptree_bind; eauto.
Qed.

(** The guarded proof follows an iteration step until it returns.  A left
    result performs the administrative [Tau] and starts the next round; a
    right result terminates. *)
Local CoFixpoint probabilistic_ptree_iter_from {I R}
    (step : I -> ptree E M (I + R))
    (Hstep : forall i, probabilistic_ptree (step i))
    (t : ptree E M (I + R))
    (Ht : probabilistic_ptree t) :
    probabilistic_ptree
      (PTree.bind t (fun lr =>
        match lr with
        | inl i' => Tau (PTree.iter step i')
        | inr r => PTree.ret r
        end)).
Proof.
  unfold probabilistic_ptree in *.
  rewrite observe_bind_probability.
  destruct (observe t) eqn:Hot.
  - cbn. dependent destruction Ht. destruct r as [i' | r].
    + constructor.
      exact (@probabilistic_ptree_iter_from
        I R step Hstep (step i') (Hstep i')).
    + constructor.
  - cbn. dependent destruction Ht. constructor.
    eapply (@probabilistic_ptree_iter_from I R step Hstep); eauto.
  - cbn. dependent destruction Ht. constructor. intro x.
    eapply (@probabilistic_ptree_iter_from I R step Hstep); eauto.
  - cbn. dependent destruction Ht. constructor.
    + assumption.
    + intro x. eapply (@probabilistic_ptree_iter_from I R step Hstep); eauto.
Qed.

(** Iteration preserves well-formedness when every unfolded step is a
    probability tree. *)
Definition probabilistic_ptree_iter {I R}
    (step : I -> ptree E M (I + R))
    (Hstep : forall i, probabilistic_ptree (step i))
    (i : I) : probabilistic_ptree (PTree.iter step i) :=
  @probabilistic_ptree_iter_from I R step Hstep (step i) (Hstep i).

End ProbabilityWellFormednessCombinators.
