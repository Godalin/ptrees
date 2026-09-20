(** Role: Canonical equational/hitting theory. Depends on Core and Prob; does not provide comparison or interpreter semantics. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Eq Require Import PrimitiveStableHitting.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Generic relational infrastructure for complete stable-hitting behavior.
    This layer knows only kernels, their stable outputs and coupling: it
    depends on neither PTree syntax nor a particular bisimulation GFP.
    PEutt and the induced stable-head transition system are separate clients.

    Matching is bidirectional over complete witnesses; no canonical measure
    representative is chosen. The endpoint lemmas below recover the coupling
    formula at chosen witnesses using the existing limit-uniqueness laws. *)
Section StableHittingMatch.
Context {MF : Type -> Type}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FO : @SemanticOmega MF FI}.
Context {S1 S2 A1 A2 : Type}.
Variable kernel1 : S1 -> MF (stable_target S1 A1).
Variable kernel2 : S2 -> MF (stable_target S2 A2).
Variable AR : (S1 -> S2 -> Prop) -> A1 -> A2 -> Prop.
Hypothesis AR_mono : forall sim1 sim2,
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall a1 a2, AR sim1 a1 a2 -> AR sim2 a1 a2.

Definition stable_hitting_match (sim : S1 -> S2 -> Prop)
    (s1 : S1) (s2 : S2) : Prop :=
  (forall out1, stable_hitting kernel1 s1 out1 ->
    exists out2, stable_hitting kernel2 s2 out2 /\
      sem_lift (AR sim) out1 out2) /\
  (forall out2, stable_hitting kernel2 s2 out2 ->
    exists out1, stable_hitting kernel1 s1 out1 /\
      sem_lift (AR sim) out1 out2).

Lemma stable_hitting_match_mono sim1 sim2 :
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall s1 s2, stable_hitting_match sim1 s1 s2 ->
    stable_hitting_match sim2 s1 s2.
Proof.
  intros Hsim s1 s2 Hmatch.
  unfold stable_hitting_match in Hmatch |- *.
  destruct Hmatch as [Hforward Hbackward]. split.
  - intros out1 Hhit1. destruct (Hforward out1 Hhit1)
      as [out2 [Hhit2 Hlift]]. exists out2. split; [exact Hhit2|].
    eapply sem_lift_mono; [|exact Hlift]. exact (AR_mono Hsim).
  - intros out2 Hhit2. destruct (Hbackward out2 Hhit2)
      as [out1 [Hhit1 Hlift]]. exists out1. split; [exact Hhit1|].
    eapply sem_lift_mono; [|exact Hlift]. exact (AR_mono Hsim).
Qed.

End StableHittingMatch.

Section StableHittingMatchEndpoint.
Context {MF : Type -> Type}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FO : @SemanticOmega MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}.
Context {S1 S2 A1 A2 : Type}.
Variable kernel1 : S1 -> MF (stable_target S1 A1).
Variable kernel2 : S2 -> MF (stable_target S2 A2).
Variable AR : (S1 -> S2 -> Prop) -> A1 -> A2 -> Prop.

(** Generator-level endpoint rule.  A pair of complete hitting witnesses and
    one coupling between them determine the full bidirectional match: all
    other complete witnesses are transported to these by uniqueness. *)
Lemma stable_hitting_match_of_hitting_lift
    (sim : S1 -> S2 -> Prop) s1 s2 out1 out2 :
  stable_hitting kernel1 s1 out1 ->
  stable_hitting kernel2 s2 out2 ->
  sem_lift (AR sim) out1 out2 ->
  stable_hitting_match kernel1 kernel2 AR sim s1 s2.
Proof.
  intros Hhit1 Hhit2 Hlift. unfold stable_hitting_match. split.
  - intros out1' Hhit1'. exists out2. split; [exact Hhit2|].
    eapply sem_lift_proper_l; [|exact Hlift].
    eapply stable_hitting_unique; [exact Hhit1|exact Hhit1'].
  - intros out2' Hhit2'. exists out1. split; [exact Hhit1|].
    eapply sem_lift_proper_r; [|exact Hlift].
    eapply stable_hitting_unique; [exact Hhit2|exact Hhit2'].
Qed.

(** Eliminate a generator match at chosen complete witnesses.  This is the
    converse-facing companion of [stable_hitting_match_of_hitting_lift] and
    is particularly useful in compatible-closure proofs: progress of a
    recursive candidate can be consumed without first folding it into the
    final greatest fixed point. *)
Lemma stable_hitting_match_hitting_lift
    (sim : S1 -> S2 -> Prop) s1 s2 out1 out2 :
  stable_hitting_match kernel1 kernel2 AR sim s1 s2 ->
  stable_hitting kernel1 s1 out1 ->
  stable_hitting kernel2 s2 out2 ->
  sem_lift (AR sim) out1 out2.
Proof.
  intros [Hforward _] Hhit1 Hhit2.
  destruct (Hforward out1 Hhit1) as [out2' [Hhit2' Hlift]].
  eapply sem_lift_proper_r; [|exact Hlift].
  eapply stable_hitting_unique; [exact Hhit2'|exact Hhit2].
Qed.

End StableHittingMatchEndpoint.
