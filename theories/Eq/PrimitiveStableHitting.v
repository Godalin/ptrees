Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Program.
From Coinduction Require Import all.
From PTree.Prob Require Import TwoLevelMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Behavior semantics for an arbitrary state-to-distribution kernel.
    Neither the state space nor the kernel contains a PTree, Bind, or Iter
    constructor.  A primitive step either reaches a stable observation or a
    residual state. *)
Polymorphic Variant stable_target (S O : Type) : Type :=
  | SHStable (out : O)
  | SHInternal (state : S).

Arguments SHStable {S O} _.
Arguments SHInternal {S O} _.

Section PrimitiveStableHitting.
Context {MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {S A : Type}.
Variable kernel : S -> MF (stable_target S A).

(** Resolve at most [fuel] residual primitive states.  Stable mass is
    retained immediately; unresolved residual mass is discarded into the
    subprobability bottom. *)
Fixpoint stable_target_approx (fuel : nat) (target : stable_target S A) :
    MF A :=
  match target with
  | SHStable out => sem_ret out
  | SHInternal state =>
      match fuel with
      | Datatypes.O => sem_zero
      | Datatypes.S fuel' =>
          sem_bind (kernel state) (stable_target_approx fuel')
      end
  end.

Definition stable_hitting_approx (fuel : nat) (state : S) : MF A :=
  sem_bind (kernel state) (stable_target_approx fuel).

Definition stable_hitting_weak (state : S) (out : MF A) : Prop :=
  sem_lub (fun fuel => stable_hitting_approx fuel state) out.

Definition stable_hitting_ast (state : S) (out : MF A) : Prop :=
  stable_hitting_weak state out /\ sem_total out.

Lemma stable_target_stableE fuel out :
  stable_target_approx fuel (SHStable out) = sem_ret out.
Proof. destruct fuel; reflexivity. Qed.

Lemma stable_target_internal_zeroE state :
  stable_target_approx Datatypes.O (SHInternal state) = sem_zero.
Proof. reflexivity. Qed.

Lemma stable_target_internal_succE fuel state :
  stable_target_approx (Datatypes.S fuel) (SHInternal state) =
    sem_bind (kernel state) (stable_target_approx fuel).
Proof. reflexivity. Qed.

End PrimitiveStableHitting.

Section PrimitiveStableHittingOrder.
Context {MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}.
Context {S A : Type}.
Variable kernel : S -> MF (stable_target S A).

Lemma stable_target_approx_increasing fuel
    (target : stable_target S A) :
  sem_le (stable_target_approx kernel fuel target)
    (stable_target_approx kernel (Datatypes.S fuel) target).
Proof.
  induction fuel as [|fuel IH] in target |- *; destruct target as [out|state].
  - apply sem_le_refl.
  - apply sem_zero_le.
  - apply sem_le_refl.
  - apply sem_bind_le_k. exact IH.
Qed.

Theorem stable_hitting_increasing state :
  sem_increasing (fun fuel => stable_hitting_approx kernel fuel state).
Proof.
  intro fuel. unfold stable_hitting_approx.
  apply sem_bind_le_k. intro target.
  exact (stable_target_approx_increasing fuel target).
Qed.

Theorem stable_hitting_mono state n m :
  Peano.le n m ->
  sem_le (stable_hitting_approx kernel n state)
    (stable_hitting_approx kernel m state).
Proof.
  intro Hnm. induction Hnm.
  - apply sem_le_refl.
  - eapply sem_le_trans; [exact IHHnm|].
    apply stable_hitting_increasing.
Qed.

End PrimitiveStableHittingOrder.

Section PrimitiveStableHittingLimits.
Context {MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}.
Context {S A : Type}.
Variable kernel : S -> MF (stable_target S A).

Theorem stable_hitting_weak_exists state :
  exists out, stable_hitting_weak kernel state out.
Proof.
  unfold stable_hitting_weak. apply sem_lub_exists.
  exact (stable_hitting_increasing kernel state).
Qed.

Theorem stable_hitting_weak_unique state out1 out2 :
  stable_hitting_weak kernel state out1 ->
  stable_hitting_weak kernel state out2 ->
  sem_eq out1 out2.
Proof.
  unfold stable_hitting_weak. intros H1 H2.
  eapply sem_lub_unique; eassumption.
Qed.

End PrimitiveStableHittingLimits.

(** Relational lifting of one primitive target.  Stable observations must
    satisfy the public result relation; internal targets remain guarded by
    the candidate state relation. *)
Polymorphic Inductive stable_target_rel {S1 S2 A1 A2}
    (RA : A1 -> A2 -> Prop) (sim : S1 -> S2 -> Prop) :
    stable_target S1 A1 -> stable_target S2 A2 -> Prop :=
  | SHTRStable a1 a2 :
      RA a1 a2 -> stable_target_rel RA sim (SHStable a1) (SHStable a2)
  | SHTRInternal s1 s2 :
      sim s1 s2 -> stable_target_rel RA sim (SHInternal s1) (SHInternal s2).

Section PrimitiveKernelBisimulation.
Context {MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {S1 S2 A1 A2 : Type}.
Variable kernel1 : S1 -> MF (stable_target S1 A1).
Variable kernel2 : S2 -> MF (stable_target S2 A2).
Variable AR : (S1 -> S2 -> Prop) -> A1 -> A2 -> Prop.
Hypothesis AR_mono : forall sim1 sim2,
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall a1 a2, AR sim1 a1 a2 -> AR sim2 a1 a2.

(** A generic divergence-sensitive probabilistic bisimulation generator.
    [SKBAST] permits different finite schedules to meet at coupled total
    stable limits.  [SKBStep] is the residual guard: programs without an AST
    limit must still expose coupled primitive steps, so absence of a weak
    transition cannot prove an arbitrary equivalence.  In particular, there
    is no coinductive one-sided silent rule: such a rule lets a silent
    self-loop absorb an arbitrary state without observing its behavior. *)
Inductive stable_kernel_bisimF (sim : S1 -> S2 -> Prop) :
    S1 -> S2 -> Prop :=
  | SKBAST s1 s2 out1 out2 :
      stable_hitting_ast kernel1 s1 out1 ->
      stable_hitting_ast kernel2 s2 out2 ->
      sem_lift (AR sim) out1 out2 ->
      stable_kernel_bisimF sim s1 s2
  | SKBStep s1 s2 :
      sem_lift (stable_target_rel (AR sim) sim)
        (kernel1 s1) (kernel2 s2) ->
      stable_kernel_bisimF sim s1 s2.

Lemma stable_target_rel_mono
    (RA1 RA2 : A1 -> A2 -> Prop)
    (sim1 sim2 : S1 -> S2 -> Prop) :
  (forall a1 a2, RA1 a1 a2 -> RA2 a1 a2) ->
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall t1 t2, stable_target_rel RA1 sim1 t1 t2 ->
    stable_target_rel RA2 sim2 t1 t2.
Proof.
  intros HRA Hsim t1 t2 Hrel. destruct Hrel.
  - constructor. exact (HRA _ _ H).
  - constructor. exact (Hsim _ _ H).
Qed.

Lemma stable_kernel_bisimF_monotone (sim1 sim2 : S1 -> S2 -> Prop) :
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall s1 s2, stable_kernel_bisimF sim1 s1 s2 ->
    stable_kernel_bisimF sim2 s1 s2.
Proof.
  intros Hsim s1 s2 Hstep. destruct Hstep.
  - eapply SKBAST; [exact H|exact H0|].
    eapply sem_lift_mono; [|exact H1].
    exact (AR_mono Hsim).
  - apply SKBStep. eapply sem_lift_mono; [|exact H].
    eapply stable_target_rel_mono.
    + exact (AR_mono Hsim).
    + exact Hsim.
Qed.

Definition stable_kernel_bisim_body sim (s1 : S1) (s2 : S2) : Prop :=
  stable_kernel_bisimF sim s1 s2.

Program Definition fstable_kernel_bisim : mon (S1 -> S2 -> Prop) :=
  {| body := stable_kernel_bisim_body |}.
Next Obligation.
  intros sim1 sim2 Hsub s1 s2 Hstep.
  eapply stable_kernel_bisimF_monotone; eauto.
Qed.

Definition stable_kernel_bisim : S1 -> S2 -> Prop :=
  gfp fstable_kernel_bisim.

Lemma stable_kernel_bisim_unfold s1 s2 :
  stable_kernel_bisim s1 s2 ->
  stable_kernel_bisimF stable_kernel_bisim s1 s2.
Proof.
  intro H. apply (gfp_pfp fstable_kernel_bisim) in H. exact H.
Qed.

Lemma stable_kernel_bisim_fold s1 s2 :
  stable_kernel_bisimF stable_kernel_bisim s1 s2 ->
  stable_kernel_bisim s1 s2.
Proof.
  intro H. unfold stable_kernel_bisim.
  apply (gfp_fp fstable_kernel_bisim). exact H.
Qed.

End PrimitiveKernelBisimulation.

Section PrimitiveKernelBisimulationReflexivity.
Context {MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {S A : Type}.
Variable kernel : S -> MF (stable_target S A).
Variable AR : (S -> S -> Prop) -> A -> A -> Prop.
Hypothesis AR_mono : forall sim1 sim2,
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall a1 a2, AR sim1 a1 a2 -> AR sim2 a1 a2.
Hypothesis AR_refl : forall sim, Reflexive sim -> Reflexive (AR sim).

Lemma stable_target_rel_refl
    (sim : S -> S -> Prop) (Hsim : Reflexive sim) :
  Reflexive (stable_target_rel (AR sim) sim).
Proof.
  intros [a|s].
  - constructor. apply AR_refl. exact Hsim.
  - constructor. apply Hsim.
Qed.

Theorem stable_kernel_bisim_refl :
  Reflexive (@stable_kernel_bisim MF FI FC FO S S A A
    kernel kernel AR AR_mono).
Proof.
  intro state. revert state. unfold stable_kernel_bisim.
  coinduction CH CIH. intro state.
  unfold stable_kernel_bisim_body.
  apply SKBStep. apply sem_lift_refl.
  apply stable_target_rel_refl. exact CIH.
Qed.

End PrimitiveKernelBisimulationReflexivity.

Section PrimitiveKernelBisimulationConverse.
Context {MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {S1 S2 A1 A2 : Type}.
Variable kernel1 : S1 -> MF (stable_target S1 A1).
Variable kernel2 : S2 -> MF (stable_target S2 A2).
Variable AR12 : (S1 -> S2 -> Prop) -> A1 -> A2 -> Prop.
Variable AR21 : (S2 -> S1 -> Prop) -> A2 -> A1 -> Prop.
Hypothesis AR12_mono : forall sim1 sim2,
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall a1 a2, AR12 sim1 a1 a2 -> AR12 sim2 a1 a2.
Hypothesis AR21_mono : forall sim1 sim2,
  (forall s2 s1, sim1 s2 s1 -> sim2 s2 s1) ->
  forall a2 a1, AR21 sim1 a2 a1 -> AR21 sim2 a2 a1.
Hypothesis AR_converse : forall sim a1 a2,
  AR12 sim a1 a2 ->
  AR21 (fun s2 s1 => sim s1 s2) a2 a1.

Lemma stable_target_rel_converse
    (sim12 : S1 -> S2 -> Prop) (sim21 : S2 -> S1 -> Prop)
    (Hsim : forall s1 s2, sim12 s1 s2 -> sim21 s2 s1) :
  forall t1 t2,
    stable_target_rel (AR12 sim12) sim12 t1 t2 ->
    stable_target_rel (AR21 sim21) sim21 t2 t1.
Proof.
  intros t1 t2 Hrel. destruct Hrel.
  - constructor. eapply AR21_mono.
    + intros s2 s1 H12. exact (Hsim _ _ H12).
    + exact (AR_converse H).
  - constructor. exact (Hsim _ _ H).
Qed.

(** Heterogeneous converse: swapping both kernels and the observation
    transformer commutes with the native greatest fixed point. *)
Theorem stable_kernel_bisim_converse : forall s1 s2,
  @stable_kernel_bisim MF FI FC FO S1 S2 A1 A2
    kernel1 kernel2 AR12 AR12_mono s1 s2 ->
  @stable_kernel_bisim MF FI FC FO S2 S1 A2 A1
    kernel2 kernel1 AR21 AR21_mono s2 s1.
Proof.
  unfold stable_kernel_bisim at 2. coinduction CH CIH.
  intros s1 s2 Hrel.
  pose proof (@stable_kernel_bisim_unfold MF FI FC FO S1 S2 A1 A2
    kernel1 kernel2 AR12 AR12_mono s1 s2 Hrel) as Hstep.
  unfold stable_kernel_bisim_body.
  destruct Hstep.
  - eapply SKBAST; [exact H0|exact H|].
    apply sem_lift_sym in H1. eapply sem_lift_mono; [|exact H1].
    intros a2 a1 Har. eapply AR21_mono.
    + intros x2 x1 H12. exact (CIH _ _ H12).
    + exact (AR_converse Har).
  - apply SKBStep. apply sem_lift_sym in H.
    eapply sem_lift_mono; [|exact H].
    intros t2 t1 Htarget.
    eapply stable_target_rel_converse; [exact CIH|exact Htarget].
Qed.

End PrimitiveKernelBisimulationConverse.

Section PrimitiveKernelBisimulationObservationMonotonicity.
Context {MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {S1 S2 A1 A2 : Type}.
Variable kernel1 : S1 -> MF (stable_target S1 A1).
Variable kernel2 : S2 -> MF (stable_target S2 A2).
Variable AR1 AR2 : (S1 -> S2 -> Prop) -> A1 -> A2 -> Prop.
Hypothesis AR1_mono : forall sim1 sim2,
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall a1 a2, AR1 sim1 a1 a2 -> AR1 sim2 a1 a2.
Hypothesis AR2_mono : forall sim1 sim2,
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall a1 a2, AR2 sim1 a1 a2 -> AR2 sim2 a1 a2.
Hypothesis AR_sub : forall sim1 sim2,
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall a1 a2, AR1 sim1 a1 a2 -> AR2 sim2 a1 a2.

Theorem stable_kernel_bisim_observation_mono : forall s1 s2,
  @stable_kernel_bisim MF FI FC FO S1 S2 A1 A2
    kernel1 kernel2 AR1 AR1_mono s1 s2 ->
  @stable_kernel_bisim MF FI FC FO S1 S2 A1 A2
    kernel1 kernel2 AR2 AR2_mono s1 s2.
Proof.
  unfold stable_kernel_bisim at 2. coinduction CH CIH.
  intros s1 s2 Hrel.
  pose proof (@stable_kernel_bisim_unfold MF FI FC FO S1 S2 A1 A2
    kernel1 kernel2 AR1 AR1_mono s1 s2 Hrel) as Hstep.
  unfold stable_kernel_bisim_body. destruct Hstep.
  - eapply SKBAST; [exact H|exact H0|].
    eapply sem_lift_mono; [|exact H1].
    intros a1 a2 Har. exact (AR_sub CIH Har).
  - apply SKBStep. eapply sem_lift_mono; [|exact H].
    intros t1 t2 Htarget. eapply stable_target_rel_mono.
    + intros a1 a2 Har. exact (AR_sub CIH Har).
    + exact CIH.
    + exact Htarget.
Qed.

End PrimitiveKernelBisimulationObservationMonotonicity.

Section PrimitiveKernelBisimulationComposition.
Context {MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {S1 S2 S3 A1 A2 A3 : Type}.
Variable kernel1 : S1 -> MF (stable_target S1 A1).
Variable kernel2 : S2 -> MF (stable_target S2 A2).
Variable kernel3 : S3 -> MF (stable_target S3 A3).
Variable AR12 : (S1 -> S2 -> Prop) -> A1 -> A2 -> Prop.
Variable AR23 : (S2 -> S3 -> Prop) -> A2 -> A3 -> Prop.
Variable AR13 : (S1 -> S3 -> Prop) -> A1 -> A3 -> Prop.
Hypothesis AR12_mono : forall sim1 sim2,
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall a1 a2, AR12 sim1 a1 a2 -> AR12 sim2 a1 a2.
Hypothesis AR23_mono : forall sim1 sim2,
  (forall s2 s3, sim1 s2 s3 -> sim2 s2 s3) ->
  forall a2 a3, AR23 sim1 a2 a3 -> AR23 sim2 a2 a3.
Hypothesis AR13_mono : forall sim1 sim2,
  (forall s1 s3, sim1 s1 s3 -> sim2 s1 s3) ->
  forall a1 a3, AR13 sim1 a1 a3 -> AR13 sim2 a1 a3.

Local Definition KB12 := @stable_kernel_bisim MF FI FC FO
  S1 S2 A1 A2 kernel1 kernel2 AR12 AR12_mono.
Local Definition KB23 := @stable_kernel_bisim MF FI FC FO
  S2 S3 A2 A3 kernel2 kernel3 AR23 AR23_mono.
Local Definition KB13 := @stable_kernel_bisim MF FI FC FO
  S1 S3 A1 A3 kernel1 kernel3 AR13 AR13_mono.

(** Composition of stable observations, parametrized by composition of the
    recursive state relations. *)
Hypothesis AR_comp : forall sim12 sim23 sim13,
  (forall s1 s3, (exists s2, sim12 s1 s2 /\ sim23 s2 s3) ->
    sim13 s1 s3) ->
  forall a1 a3, (exists a2, AR12 sim12 a1 a2 /\ AR23 sim23 a2 a3) ->
    AR13 sim13 a1 a3.

(** These are the exact mixed-scale obligations exposed by AST x Step and
    Step x AST.  They are intentionally hypotheses here: deriving them from
    primitive couplings requires an additional stable-hitting continuity
    theorem, not merely coupling gluing. *)
Hypothesis KB12_ast_backward : forall s1 s2,
  KB12 s1 s2 -> forall out2,
  stable_hitting_ast kernel2 s2 out2 ->
  exists out1, stable_hitting_ast kernel1 s1 out1 /\
    sem_lift (AR12 KB12) out1 out2.
Hypothesis KB23_ast_forward : forall s2 s3,
  KB23 s2 s3 -> forall out2,
  stable_hitting_ast kernel2 s2 out2 ->
  exists out3, stable_hitting_ast kernel3 s3 out3 /\
    sem_lift (AR23 KB23) out2 out3.

Lemma stable_target_rel_compose
    (sim13 : S1 -> S3 -> Prop)
    (Hsim : forall s1 s3, (exists s2, KB12 s1 s2 /\ KB23 s2 s3) ->
      sim13 s1 s3) :
  forall t1 t3,
    (exists t2,
      stable_target_rel (AR12 KB12) KB12 t1 t2 /\
      stable_target_rel (AR23 KB23) KB23 t2 t3) ->
    stable_target_rel (AR13 sim13) sim13 t1 t3.
Proof.
  intros t1 t3 [t2 [H12 H23]].
  destruct H12; inversion H23; subst.
  - constructor. eapply AR_comp.
    + exact Hsim.
    + eauto.
  - constructor. apply Hsim. eauto.
Qed.

(** Conditional heterogeneous transitivity.  After removing unrestricted
    silent stuttering, the only non-algebraic premise is preservation of AST
    stable hitting across the two component bisimulations. *)
Theorem stable_kernel_bisim_compose_rel : forall s1 s3,
  (exists s2, KB12 s1 s2 /\ KB23 s2 s3) -> KB13 s1 s3.
Proof.
  unfold KB13. unfold stable_kernel_bisim at 1. coinduction CH CIH.
  intros s1 s3 [s2 [H12 H23]].
  pose proof (@stable_kernel_bisim_unfold MF FI FC FO S1 S2 A1 A2
    kernel1 kernel2 AR12 AR12_mono s1 s2 H12) as Hstep12.
  unfold stable_kernel_bisim_body. destruct Hstep12.
  - destruct (KB23_ast_forward H23 H0)
      as [out3 [Hast3 Hlift23]].
    eapply SKBAST; [exact H|exact Hast3|].
    pose proof (sem_lift_comp H1 Hlift23) as Hcomp.
    eapply sem_lift_mono; [|exact Hcomp].
    intros a1 a3 [a2 [Ha12 Ha23]].
    eapply AR_comp.
    + intros x1 x3 [x2 [Hx12 Hx23]]. exact (CIH _ _ (ex_intro _ x2 (conj Hx12 Hx23))).
    + eauto.
  - pose proof (@stable_kernel_bisim_unfold MF FI FC FO S2 S3 A2 A3
      kernel2 kernel3 AR23 AR23_mono s2 s3 H23) as Hstep23.
    destruct Hstep23.
    + destruct (KB12_ast_backward H12 H0)
      as [out0 [Hast0 Hlift12]].
      eapply SKBAST; [exact Hast0|exact H1|].
      pose proof (sem_lift_comp Hlift12 H2) as Hcomp.
      eapply sem_lift_mono; [|exact Hcomp].
      intros a1 a3 [a2 [Ha12 Ha23]].
      eapply AR_comp.
      * intros x1 x3 [x2 [Hx12 Hx23]].
        exact (CIH _ _ (ex_intro _ x2 (conj Hx12 Hx23))).
      * eauto.
    + apply SKBStep.
      pose proof (sem_lift_comp H H0) as Hcomp.
      eapply sem_lift_mono; [|exact Hcomp].
      intros t1 t3 Htargets.
      eapply stable_target_rel_compose.
      * intros x1 x3 [x2 [Hx12 Hx23]].
        exact (CIH _ _ (ex_intro _ x2 (conj Hx12 Hx23))).
      * exact Htargets.
Qed.

Corollary stable_kernel_bisim_compose : forall s1 s2 s3,
  KB12 s1 s2 -> KB23 s2 s3 -> KB13 s1 s3.
Proof. intros s1 s2 s3 H12 H23. apply stable_kernel_bisim_compose_rel. eauto. Qed.

End PrimitiveKernelBisimulationComposition.
