Set Universe Polymorphism.
From PTree.Prob Require Import TwoLevelMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** An explicit joint-measure certificate.  This is not a new capability
    axiom, nor a claim that every abstract [sem_lift] has such a witness.
    The two graph couplings retain the backend's own notion of marginals;
    no equality-reflection or representation equality is assumed. *)
Section JointMeasure.
Context {M : Type -> Type} `{MI : SemanticMeasure M}.

Definition semantic_coupling {A B} (R : A -> B -> Prop)
    (mu : M A) (nu : M B) (joint : M (A * B)) : Prop :=
  sem_lift (fun p x => fst p = x) joint mu /\
  sem_lift (fun p y => snd p = y) joint nu /\
  sem_ae joint (fun p => R (fst p) (snd p)).

Context `{MC : @SemanticMeasureCoreLaws M MI}
  `{MCAE : @SemanticMeasureCouplingAELaws M MI}.

(** Change marginal representations without selecting a new joint.  This
    uses equality lifting, not representation equality or equality
    reflection; it therefore also applies to quotient-level rewrites. *)
Lemma semantic_coupling_transport {A B} (R : A -> B -> Prop)
    (mu mu' : M A) (nu nu' : M B) joint :
  sem_lift eq mu mu' -> sem_lift eq nu nu' ->
  semantic_coupling R mu nu joint -> semantic_coupling R mu' nu' joint.
Proof.
  intros Hmu Hnu [Hl [Hr Hae]]. split.
  - eapply sem_lift_mono with
      (R := fun p x => exists z, fst p = z /\ z = x).
    + intros p x [z [Hp ->]]. exact Hp.
    + eapply sem_lift_comp; eassumption.
  - split.
    + eapply sem_lift_mono with
        (R := fun p y => exists z, snd p = z /\ z = y).
      * intros p y [z [Hp ->]]. exact Hp.
      * eapply sem_lift_comp; eassumption.
    + exact Hae.
Qed.

Lemma semantic_coupling_left_supported {A B} (R : A -> B -> Prop)
    (mu : M A) (nu : M B) joint :
  semantic_coupling R mu nu joint ->
  sem_lift (fun p x => fst p = x /\ R (fst p) (snd p)) joint mu.
Proof.
  intros [Hl [Hr Hae]]. eapply sem_lift_mono with
    (R := fun p x => fst p = x /\ R (fst p) (snd p) /\ True).
  - intros p x [Hpx [Hp _]]. split; assumption.
  - eapply sem_lift_ae_restrict; [exact Hl|exact Hae|apply sem_ae_true].
Qed.

Lemma semantic_coupling_right_supported {A B} (R : A -> B -> Prop)
    (mu : M A) (nu : M B) joint :
  semantic_coupling R mu nu joint ->
  sem_lift (fun p y => snd p = y /\ R (fst p) (snd p)) joint nu.
Proof.
  intros [Hl [Hr Hae]]. eapply sem_lift_mono with
    (R := fun p y => snd p = y /\ R (fst p) (snd p) /\ True).
  - intros p y [Hpy [Hp _]]. split; assumption.
  - eapply sem_lift_ae_restrict; [exact Hr|exact Hae|apply sem_ae_true].
Qed.

Lemma semantic_coupling_sound {A B} (R : A -> B -> Prop)
    (mu : M A) (nu : M B) joint :
  semantic_coupling R mu nu joint -> sem_lift R mu nu.
Proof.
  intro Hjoint. eapply sem_lift_mono with
    (R := fun x y => exists p : A * B,
      (fst p = x /\ R (fst p) (snd p)) /\ snd p = y).
  - intros x y [p [[Hx HR] Hy]]. subst x y. exact HR.
  - eapply sem_lift_comp.
    + apply sem_lift_sym. exact (semantic_coupling_left_supported Hjoint).
    + exact (proj1 (proj2 Hjoint)).
Qed.

Context `{MB : @SemanticMeasureBindLaws M MI}.

(** A continuation may depend on the whole sampled pair.  The premise is
    only needed on the joint's support, not on all Cartesian-product pairs.
    This is the probabilistic replacement for choosing an arbitrary partner
    from an existential support fact, which would lose its marginal law. *)
Lemma semantic_coupling_dependent_bind {A B C D}
    (R : A -> B -> Prop) (T : C -> D -> Prop)
    (mu : M A) (nu : M B) joint
    (left : A * B -> M C) (right : A * B -> M D) :
  semantic_coupling R mu nu joint ->
  (forall x y, R x y -> sem_lift T (left (x,y)) (right (x,y))) ->
  sem_lift T (sem_bind joint left) (sem_bind joint right).
Proof.
  intros [_ [_ Hae]] Hstep.
  eapply sem_lift_bind with
    (R := fun p q => p = q /\ R (fst p) (snd p)).
  - eapply sem_lift_mono with
      (R := fun p q => p = q /\ R (fst p) (snd p) /\ True).
    + intros p q [-> [Hp _]]. split; [reflexivity|exact Hp].
    + eapply sem_lift_ae_restrict;
        [apply sem_lift_refl; intros p; reflexivity|exact Hae|apply sem_ae_true].
  - intros [x y] q [<- Hp]. apply Hstep. exact Hp.
Qed.

Lemma semantic_coupling_dependent_bind_left {A B C}
    (R : A -> B -> Prop) (mu : M A) (nu : M B) joint
    (dependent : A * B -> M C) (marginal : A -> M C) :
  semantic_coupling R mu nu joint ->
  (forall x y, R x y -> sem_lift eq (dependent (x,y)) (marginal x)) ->
  sem_lift eq (sem_bind joint dependent) (sem_bind mu marginal).
Proof.
  intros Hjoint Hstep.
  eapply sem_lift_bind; [exact (semantic_coupling_left_supported Hjoint)|].
  intros [x y] z [<- HR]. apply Hstep. exact HR.
Qed.

Lemma semantic_coupling_dependent_bind_right {A B C}
    (R : A -> B -> Prop) (mu : M A) (nu : M B) joint
    (dependent : A * B -> M C) (marginal : B -> M C) :
  semantic_coupling R mu nu joint ->
  (forall x y, R x y -> sem_lift eq (dependent (x,y)) (marginal y)) ->
  sem_lift eq (sem_bind joint dependent) (sem_bind nu marginal).
Proof.
  intros Hjoint Hstep.
  eapply sem_lift_bind; [exact (semantic_coupling_right_supported Hjoint)|].
  intros [x y] z [<- HR]. apply Hstep. exact HR.
Qed.

Context `{MAE : @SemanticMeasureAEKleisliLaws M MI}.

(** Compose joint witnesses without erasing the dependency of the next
    coupling on the entire current pair.  The resulting marginals are
    integrals on that SAME joint, not independently chosen kernels. *)
Lemma semantic_coupling_bind_dependent {A B C D}
    (R : A -> B -> Prop) (T : C -> D -> Prop)
    (mu : M A) (nu : M B) joint
    (left : A * B -> M C) (right : A * B -> M D)
    (next_joint : A * B -> M (C * D)) :
  semantic_coupling R mu nu joint ->
  (forall x y, R x y ->
    semantic_coupling T (left (x,y)) (right (x,y)) (next_joint (x,y))) ->
  semantic_coupling T (sem_bind joint left) (sem_bind joint right)
    (sem_bind joint next_joint).
Proof.
  intros Hjoint Hnext. split.
  - eapply semantic_coupling_dependent_bind; [exact Hjoint|].
    intros x y Hxy. exact (proj1 (Hnext x y Hxy)).
  - split.
    + eapply semantic_coupling_dependent_bind; [exact Hjoint|].
      intros x y Hxy. exact (proj1 (proj2 (Hnext x y Hxy))).
    + eapply sem_ae_bind with (P := fun p => R (fst p) (snd p)).
      * exact (proj2 (proj2 Hjoint)).
      * intros [x y] Hxy. exact (proj2 (proj2 (Hnext x y Hxy))).
Qed.

End JointMeasure.
