(** Behavioral replacement of arbitrary handlers. Relate two complete-frontier
    machines; handler returns remain internal transitions. Adequacy is applied
    independently to each machine, never assumed as a new capability. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms RelationClasses.
From PTree.Core Require Import PTreeDefinition Handler.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder RelationalClosure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel
  PEutt RelationalHitting StableHittingRelation.
From PTree.Interp Require Import Kernel RelationalPreservation
  HandlerMachine HandlerMachineAcceleration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section HandlerEquivalence.
Context {E F MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}.

Definition peutt_handler (h1 h2 : Handler MN E F) : Prop :=
  forall X (e : E X), @peutt F MN MF FI FC MX FO X X eq (h1 X e) (h2 X e).

(** Explicit constructor; do not add a global handler/route search instance. *)
Lemma peutt_handler_equivalence : Equivalence peutt_handler.
Proof.
  split.
  - intros h X e. apply peutt_refl.
  - intros h g H X e. apply peutt_sym. apply H.
  - intros h g k H G X e. eapply peutt_trans; [apply H|apply G].
Qed.
End HandlerEquivalence.

Section HandlerReplacement.
Context {E F MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{BindOrd : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MixedOrd : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variables (Hzero : relational_zero FO) (Hlimit : relational_lub FO).
Variables h1 h2 : Handler MN E F.
Hypothesis Hhandlers : peutt_handler (MF := MF) h1 h2.
Context {A B : Type} (RR : A -> B -> Prop).

Local Notation source_rel := (@peutt E MN MF FI FC MX FO A B RR).
Local Notation candidate := (interp_rel_candidate (MF := MF) RR h1 h2).
Local Notation heads_rel := (@ptree_stable_head_rel F MN A B RR
  (@bind_upto_closure F MN MF FI FC MX FO A B RR candidate)).

Inductive handler_pair_rel :
    @handler_config E F MN A -> @handler_config E F MN B -> Prop :=
| RelatedSources t u : source_rel t u ->
    handler_pair_rel (SourceConfig t) (SourceConfig u)
| RelatedHandlers {X} (active1 active2 : ptree F MN X)
    (k1 : X -> ptree E MN A) (k2 : X -> ptree E MN B) :
    @peutt F MN MF FI FC MX FO X X eq active1 active2 ->
    (forall x, source_rel (k1 x) (k2 x)) ->
    handler_pair_rel (HandlerConfig active1 k1) (HandlerConfig active2 k2).

Lemma handler_pair_front {X} (k1 : X -> ptree E MN A)
    (k2 : X -> ptree E MN B)
    (Hk : forall x, source_rel (k1 x) (k2 x)) a b :
  @ptree_stable_head_rel F MN X X eq
    (@peutt_state F MN MF FI FC MX FO X X eq) a b ->
  stable_target_rel handler_pair_rel heads_rel
    (handler_front_result h1 k1 a) (handler_front_result h2 k2 b).
Proof.
  intro Hheads. inversion Hheads as [r1 r2 Hr|Y e c1 c2 Hc]; subst;
    cbn [handler_front_result stable_target_rel].
  - constructor. apply Hk.
  - constructor. intro y. right. right.
    exists X, X, (@eq X), (c1 y), (c2 y),
      (fun x => PTree.interp h1 (k1 x)),
      (fun x => PTree.interp h2 (k2 x)).
    split; [reflexivity|]. split; [reflexivity|].
    split; [apply Hc|]. intros x x' ->. left.
    exists (k1 x'), (k2 x'). repeat split; try reflexivity. apply Hk.
Qed.

Theorem handler_pair_kernel c d :
  handler_pair_rel c d ->
  sem_lift (stable_target_rel handler_pair_rel heads_rel)
    (handler_machine_kernel h1 c) (handler_machine_kernel h2 d).
Proof.
  intro H. destruct H as [t u Htu|X a b k1 k2 Hab Hk];
    unfold handler_machine_kernel.
  - eapply sem_lift_bind.
    + eapply peutt_state_hitting_lift;
        [exact Htu|apply handler_complete_front_hitting|apply handler_complete_front_hitting].
    + intros a b Hab. inversion Hab; subst; apply sem_lift_ret;
        cbn [source_front_result stable_target_rel].
      * constructor. assumption.
      * constructor; [apply Hhandlers|assumption].
  - eapply sem_lift_bind.
    + eapply peutt_state_hitting_lift;
        [exact Hab|apply handler_complete_front_hitting|apply handler_complete_front_hitting].
    + intros a' b' Hheads. apply sem_lift_ret.
      exact (handler_pair_front Hk Hheads).
Qed.

Theorem handler_pair_complete c d mu nu :
  handler_pair_rel c d ->
  stable_hitting (handler_machine_kernel h1) c mu ->
  stable_hitting (handler_machine_kernel h2) d nu ->
  sem_lift heads_rel mu nu.
Proof.
  apply (stable_hitting_rel (relational_bind_of_laws FB) Hzero handler_pair_kernel Hlimit).
Qed.

Theorem handler_pair_vis_fusion :
  interp_rel_vis_fusion (MF := MF) RR h1 h2.
Proof.
  intros X e k1 k2 Hk.
  destruct (stable_hitting_exists (FI := FI) (FO := FO)
    (handler_machine_kernel h1) (HandlerConfig (@h1 X e) k1)) as [mu Hmu].
  destruct (stable_hitting_exists (FI := FI) (FO := FO)
    (handler_machine_kernel h2) (HandlerConfig (@h2 X e) k2)) as [nu Hnu].
  eapply stable_hitting_match_of_hitting_lift with (out1 := mu) (out2 := nu).
  - apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
    exact (handler_machine_hitting_sound (Directed := Directed) Hmu).
  - apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
    exact (handler_machine_hitting_sound (Directed := Directed) Hnu).
  - eapply handler_pair_complete.
    + constructor; [apply Hhandlers|exact Hk].
    + exact Hmu.
    + exact Hnu.
Qed.

Theorem peutt_interp_handler_rel
    (t : ptree E MN A) (u : ptree E MN B) :
  source_rel t u ->
  @peutt F MN MF FI FC MX FO A B RR
    (PTree.interp h1 t) (PTree.interp h2 u).
Proof.
  apply peutt_interp_rel_of_vis_fusion.
  apply handler_pair_vis_fusion.
Qed.

End HandlerReplacement.

(** Clients may register this locally for setoid rewriting. *)
Section HandlerProper.
Context {E F MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{BindOrd : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MixedOrd : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variables (Hzero : relational_zero FO) (Hlimit : relational_lub FO).

Lemma peutt_interp_handler_Proper {A} :
  Proper (peutt_handler (MF := MF) ==>
    @peutt E MN MF FI FC MX FO A A eq ==>
    @peutt F MN MF FI FC MX FO A A eq)
    (fun h t => @PTree.interp E F MN h A t).
Proof.
  intros h g H t u Htu.
  exact (peutt_interp_handler_rel Hzero Hlimit H Htu).
Qed.

(** [interp] places its return carrier after the handler. This dependent
    morphism lets rewriting descend through that actual polymorphic API. *)
Lemma peutt_interp_handler_polymorphic_Proper :
  Proper (peutt_handler (MF := MF) ==>
    forall_relation (fun A =>
      @peutt E MN MF FI FC MX FO A A eq ==>
      @peutt F MN MF FI FC MX FO A A eq)) (@PTree.interp E F MN).
Proof.
  intros h g H A t u Htu.
  exact (peutt_interp_handler_rel Hzero Hlimit H Htu).
Qed.

End HandlerProper.
