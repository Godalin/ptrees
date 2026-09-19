Set Universe Polymorphism.
From Coq Require Import Logic.ClassicalChoice.
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

Lemma semantic_coupling_mono {A B} (R T : A -> B -> Prop)
    (mu : M A) (nu : M B) joint :
  (forall x y, R x y -> T x y) ->
  semantic_coupling R mu nu joint -> semantic_coupling T mu nu joint.
Proof.
  intros Hsub [Hl [Hr Hae]]. split; [exact Hl|]. split; [exact Hr|].
  eapply sem_ae_mono; [|exact Hae]. intros [x y] Hxy. apply Hsub. exact Hxy.
Qed.

(** Restricting the relation by AE properties of the marginals retains
    the SAME joint; no conditioning or renormalization is performed. *)
Lemma semantic_coupling_ae_restrict {A B} (R : A -> B -> Prop)
    (mu : M A) (nu : M B) joint (P : A -> Prop) (Q : B -> Prop) :
  semantic_coupling R mu nu joint -> sem_ae mu P -> sem_ae nu Q ->
  semantic_coupling (fun x y => R x y /\ P x /\ Q y) mu nu joint.
Proof.
  intros [Hl [Hr Hae]] HP HQ. split; [exact Hl|]. split; [exact Hr|].
  apply sem_ae_conj; [exact Hae|]. apply sem_ae_conj.
  - eapply sem_ae_mono; [|exact (sem_lift_ae_transport_r (sem_lift_sym Hl) HP)].
    intros p [x [Hx HPx]]. rewrite Hx. exact HPx.
  - eapply sem_ae_mono; [|exact (sem_lift_ae_transport_r (sem_lift_sym Hr) HQ)].
    intros p [y [Hy HQy]]. rewrite Hy. exact HQy.
Qed.

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

(** Realization is closed under the ordinary relational bind rule.  The
    chosen branch joint depends on BOTH source values, but its marginals
    are precisely [k x] and [h y].  The conclusion keeps the original
    marginal binds, rather than replacing them by integrals on the joint. *)
Theorem semantic_coupling_bind {A B C D}
    (R : A -> B -> Prop) (T : C -> D -> Prop)
    (mu : M A) (nu : M B) joint
    (k : A -> M C) (h : B -> M D)
    (next_joint : A * B -> M (C * D)) :
  semantic_coupling R mu nu joint ->
  (forall x y, R x y -> semantic_coupling T (k x) (h y) (next_joint (x,y))) ->
  semantic_coupling T (sem_bind mu k) (sem_bind nu h)
    (sem_bind joint next_joint).
Proof.
  intros Hjoint Hnext. split.
  - eapply sem_lift_bind; [exact (semantic_coupling_left_supported Hjoint)|].
    intros [x y] z [<- Hxy]. exact (proj1 (Hnext x y Hxy)).
  - split.
    + eapply sem_lift_bind; [exact (semantic_coupling_right_supported Hjoint)|].
      intros [x y] z [<- Hxy]. exact (proj1 (proj2 (Hnext x y Hxy))).
    + eapply sem_ae_bind with (P := fun p => R (fst p) (snd p)).
      * exact (proj2 (proj2 Hjoint)).
      * intros [x y] Hxy. exact (proj2 (proj2 (Hnext x y Hxy))).
Qed.

(** The existential version matches the induction hypotheses of a lifting
    derivation.  Off the related support, an ordinary product provides a
    default measure; neither inhabited value types nor zero/omega or
    commutativity capabilities are needed. *)
Theorem semantic_coupling_bind_realization {A B C D}
    (R : A -> B -> Prop) (T : C -> D -> Prop)
    (mu : M A) (nu : M B) (k : A -> M C) (h : B -> M D) :
  (exists joint, semantic_coupling R mu nu joint) ->
  (forall x y, R x y -> exists joint, semantic_coupling T (k x) (h y) joint) ->
  exists joint, semantic_coupling T (sem_bind mu k) (sem_bind nu h) joint.
Proof.
  intros [joint Hjoint] Hbranches.
  assert (Hex : forall p : A * B, exists branch : M (C * D),
    R (fst p) (snd p) -> semantic_coupling T (k (fst p)) (h (snd p)) branch).
  { intros [x y]. destruct (classic (R x y)) as [Hxy|Hnot].
    - destruct (Hbranches x y Hxy) as [branch Hbranch].
      exists branch. intros _. exact Hbranch.
    - exists (sem_bind (k x) (fun c => sem_bind (h y) (fun d => sem_ret (c,d)))).
      intro Hxy. contradiction. }
  destruct (choice _ Hex) as [next_joint Hnext].
  exists (sem_bind joint next_joint).
  eapply semantic_coupling_bind; [exact Hjoint|].
  intros x y Hxy. exact (Hnext (x,y) Hxy).
Qed.

End JointMeasure.
