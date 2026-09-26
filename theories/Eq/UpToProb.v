(** Coinduction up to one coupled native sampling context.  This is a
    proof closure, not a new behavioral relation.  A candidate must still
    progress through the complete stable-hitting generator: an internal
    [Prob] node alone is not a coinductive guard. *)
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Eq Require Import PrimitiveStableHitting PTreeKernel
  StableHittingRelation PEutt.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section UpToProb.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FO : @SemanticOmega MF FI} `{MX : MixedMeasure MN MF}.
Context {A B : Type} (RR : A -> B -> Prop).
Local Notation state1 := (ptree' E MN A).
Local Notation state2 := (ptree' E MN B).
Local Notation W := (@peutt_state E MN MF FI FC MX FO A B RR).
Local Notation matches := (stable_hitting_match
  (@ptree_primitive_kernel E MN MF FI MX A)
  (@ptree_primitive_kernel E MN MF FI MX B)
  (@ptree_stable_head_rel E MN A B RR)).

Definition prob_upto_closure (sim : state1 -> state2 -> Prop)
    (s1 : state1) (s2 : state2) : Prop :=
  sim s1 s2 \/ W s1 s2 \/
  exists (X Y : Type) (XR : X -> Y -> Prop)
    (mu : MN X) (nu : MN Y)
    (k : X -> ptree E MN A) (h : Y -> ptree E MN B),
    s1 = observe (Prob mu k) /\ s2 = observe (Prob nu h) /\
    sem_lift XR mu nu /\
    (forall x y, XR x y ->
      sim (observe (k x)) (observe (h y)) \/ peutt RR (k x) (h y)).

Lemma prob_upto_closure_includes sim s1 s2 :
  sim s1 s2 -> prob_upto_closure sim s1 s2.
Proof. intro H. left. exact H. Qed.

Lemma prob_upto_closure_mono sim1 sim2 :
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall s1 s2, prob_upto_closure sim1 s1 s2 ->
    prob_upto_closure sim2 s1 s2.
Proof.
  intros Hsub s1 s2 [Hr|[Hw|Hs]].
  - left. exact (Hsub _ _ Hr).
  - right. left. exact Hw.
  - destruct Hs as (X & Y & XR & mu & nu & k & h & -> & -> & Hmu & Hk).
    right. right. exists X, Y, XR, mu, nu, k, h.
    repeat split; try reflexivity; try assumption.
    intros x y Hxy. destruct (Hk x y Hxy) as [Hr|Hw].
    + left. exact (Hsub _ _ Hr).
    + right. exact Hw.
Qed.

Lemma prob_upto_closure_sample sim X Y (XR : X -> Y -> Prop)
    (mu : MN X) (nu : MN Y) k h :
  sem_lift XR mu nu ->
  (forall x y, XR x y ->
    sim (observe (k x)) (observe (h y)) \/ peutt RR (k x) (h y)) ->
  prob_upto_closure sim (observe (Prob mu k)) (observe (Prob nu h)).
Proof.
  intros Hmu Hk. right. right.
  exists X, Y, XR, mu, nu, k, h. repeat split; assumption || reflexivity.
Qed.

Context `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MixedOmega : @MixedMeasureOmegaLaws MN MF NI FI MX FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.

(** The recursive branch consumes [Hprogress] at complete hitting
    witnesses.  It never invokes [peutt_prob] on the candidate.  Relational
    mixed bind pushes the native coupling to the two complete frontiers. *)
Lemma prob_upto_closure_compatible sim
    (Hprogress : forall s1 s2, sim s1 s2 ->
      matches (prob_upto_closure sim) s1 s2) :
  forall s1 s2, prob_upto_closure sim s1 s2 ->
    matches (prob_upto_closure sim) s1 s2.
Proof.
  assert (Hknown : forall s1 s2, W s1 s2 ->
      matches (prob_upto_closure sim) s1 s2).
  { intros s1 s2 H.
    apply stable_hitting_bisim_unfold in H.
    eapply stable_hitting_match_mono; [| |exact H].
    - exact (ptree_stable_head_rel_mono (RR := RR)).
    - intros x y Hxy. right. left. exact Hxy. }
  intros s1 s2 [Hr|[Hw|Hs]].
  - exact (Hprogress _ _ Hr).
  - exact (Hknown _ _ Hw).
  - destruct Hs as (X & Y & XR & mu & nu & k & h & -> & -> & Hmu & Hk).
    destruct (stable_hitting_front_choice k) as [front1 Hfront1].
    destruct (stable_hitting_front_choice h) as [front2 Hfront2].
    eapply stable_hitting_match_of_hitting_lift.
    + eapply stable_hitting_prob with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros x _. exact (Hfront1 x).
    + eapply stable_hitting_prob with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros y _. exact (Hfront2 y).
    + eapply mixed_lift_bind; [exact Hmu|].
      intros x y Hxy.
      eapply stable_hitting_match_hitting_lift;
        [|exact (Hfront1 x)|exact (Hfront2 y)].
      destruct (Hk x y Hxy) as [Hr|Hw].
      * exact (Hprogress _ _ Hr).
      * exact (Hknown _ _ Hw).
Qed.

Theorem peutt_coinduction_upto_prob sim
    (Hprogress : forall s1 s2, sim s1 s2 ->
      matches (prob_upto_closure sim) s1 s2) t u :
  sim (observe t) (observe u) -> peutt RR t u.
Proof.
  intro Hsim. eapply peutt_coinduction_upto_closure
    with (clo := prob_upto_closure) (sim := sim).
  - exact prob_upto_closure_includes.
  - exact prob_upto_closure_compatible.
  - exact Hprogress.
  - exact Hsim.
Qed.
End UpToProb.
