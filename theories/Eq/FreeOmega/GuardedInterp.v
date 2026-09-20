Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.
From PTree.Eq.FreeOmega Require Import Base Relation Bind Interp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Semantic visible guarding: only the complete behavior matters, not a
    syntactic prefix or a bound on the number of internal computations.
    Missing mass is permitted, including complete internal divergence. *)
Definition stable_head_is_visible {E MN R} (h : stable_head E MN R) : Prop :=
  match h with FHRet _ => False | @FHVis _ _ _ _ _ _ => True end.

Section GuardedInterp.
Context {E F MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI} `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NC := NC) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Variable handler : forall X, E X -> ptree F MN X.

Definition guarded_handler : Prop :=
  forall X (e : E X) out,
    @ptree_stable_hitting F MN MF FI FreeOmegaMixedMeasure FO X
      (observe (handler e)) out ->
    @sem_ae MF FI _ out stable_head_is_visible.

Context `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}.

(** A convenient complete witness suffices; the public contract holds for
    every representative, by uniqueness and coupling support transport. *)
Lemma guarded_handler_of_hitting
    (H : forall X (e : E X), exists out,
      @ptree_stable_hitting F MN MF FI FreeOmegaMixedMeasure FO X
        (observe (handler e)) out /\
      @sem_ae MF FI _ out stable_head_is_visible) : guarded_handler.
Proof.
  intros X e out Hout. destruct (H X e) as [mu [Hmu Hae]].
  assert (Heq : @sem_eq MF FI _ mu out).
  { eapply stable_hitting_unique; eassumption. }
  pose proof (proj1 (free_omega_qlift_support Heq) _ Hae) as Htransport.
  eapply free_omega_ae_mono; [|exact Htransport].
  intros h [h' [-> Hvisible]]. exact Hvisible.
Qed.

Theorem guarded_handler_vis_fusion {A B} (RR : A -> B -> Prop)
    (Hguard : guarded_handler) :
  interp_vis_fusion (NI := NI) (NO := NO) RR handler.
Proof.
  intros X e k1 k2 Hk.
  destruct (stable_hitting_exists (FI := FI) (FO := FO)
    (@ptree_primitive_kernel F MN MF FI FreeOmegaMixedMeasure X)
    (observe (handler e))) as [mu Hmu].
  destruct (stable_hitting_front_choice (FI := FI) (FO := FO)
    (fun x => PTree.interp handler (k1 x))) as [front1 Hfront1].
  destruct (stable_hitting_front_choice (FI := FI) (FO := FO)
    (fun x => PTree.interp handler (k2 x))) as [front2 Hfront2].
  eapply stable_hitting_match_of_hitting_lift
    with (out1 := sem_bind mu (stable_head_bind_front
      (fun x => PTree.interp handler (k1 x)) front1))
         (out2 := sem_bind mu (stable_head_bind_front
      (fun x => PTree.interp handler (k2 x)) front2)).
  - apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
    eapply (ptree_stable_hitting_bind (FI := FI) (FO := FO)
      (MX := FreeOmegaMixedMeasure)); [apply ptree_bind_cofinal_all|exact Hmu|exact Hfront1].
  - apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
    eapply (ptree_stable_hitting_bind (FI := FI) (FO := FO)
      (MX := FreeOmegaMixedMeasure)); [apply ptree_bind_cofinal_all|exact Hmu|exact Hfront2].
  - assert (Hdiag : @sem_lift MF FI _ _ eq mu mu).
    { apply sem_lift_refl. intro h. reflexivity. }
    pose proof (sem_lift_ae_restrict Hdiag (Hguard X e mu Hmu) (Hguard X e mu Hmu)) as Hrestricted.
    eapply (sem_lift_bind (SI := FI)); [exact Hrestricted|].
    intros h h' [-> [Hvisible _]]. destruct h' as [r|Y f c]; [contradiction|].
    apply (sem_lift_ret (SI := FI)). constructor. intro y.
    right. right.
    exists X, X, (@eq X), (c y), (c y),
      (fun x => PTree.interp handler (k1 x)),
      (fun x => PTree.interp handler (k2 x)).
    split; [reflexivity|]. split; [reflexivity|].
    split; [apply peutt_refl|].
    intros x x' ->. left.
    exists (k1 x'), (k2 x').
    split; [reflexivity|]. split; [reflexivity|]. apply Hk.
Qed.

Theorem peutt_interp_guarded {A B} (RR : A -> B -> Prop)
    (Hguard : guarded_handler) (t1 : ptree E MN A) (t2 : ptree E MN B) :
  @peutt E MN MF FI FC FreeOmegaMixedMeasure FO A B RR t1 t2 ->
  @peutt F MN MF FI FC FreeOmegaMixedMeasure FO A B RR
    (PTree.interp handler t1) (PTree.interp handler t2).
Proof.
  apply (peutt_interp_of_vis_fusion (NI := NI) (NC := NC) (NAE := NAE)
    (NO := NO) (NCAEInterp := NCAE) (NCountAEInterp := NCount)).
  exact (guarded_handler_vis_fusion (RR := RR) Hguard).
Qed.

(** Guardedness is an explicit local premise, not a globally synthesized
    typeclass obligation or an assumption on every effect handler. *)
Lemma peutt_interp_guarded_Proper {R} (Hguard : guarded_handler) :
  Proper (@peutt E MN MF FI FC FreeOmegaMixedMeasure FO R R eq ==>
          @peutt F MN MF FI FC FreeOmegaMixedMeasure FO R R eq)
    (@PTree.interp E F MN handler R).
Proof. intros t u Htu. exact (peutt_interp_guarded Hguard Htu). Qed.
End GuardedInterp.
