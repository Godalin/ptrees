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

Definition stable_kernel_silent_l (s1 s1' : S1) : Prop :=
  sem_eq (kernel1 s1) (sem_ret (SHInternal s1')).

Definition stable_kernel_silent_r (s2 s2' : S2) : Prop :=
  sem_eq (kernel2 s2) (sem_ret (SHInternal s2')).

(** A generic divergence-sensitive probabilistic bisimulation generator.
    [SKBAST] permits different finite schedules to meet at coupled total
    stable limits.  [SKBStep] is the residual guard: programs without an AST
    limit must still expose coupled primitive steps, so absence of a weak
    transition cannot prove an arbitrary equivalence. *)
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
      stable_kernel_bisimF sim s1 s2
  | SKBSilentL s1 s1' s2 :
      stable_kernel_silent_l s1 s1' ->
      sim s1' s2 ->
      stable_kernel_bisimF sim s1 s2
  | SKBSilentR s1 s2 s2' :
      stable_kernel_silent_r s2 s2' ->
      sim s1 s2' ->
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
  - eapply SKBSilentL; [exact H|exact (Hsim _ _ H0)].
  - eapply SKBSilentR; [exact H|exact (Hsim _ _ H0)].
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

(** Audit witness: the unrestricted coinductive one-sided silent rule makes
    a semantic silent self-loop absorb every state on the other side.  This
    theorem is intentionally stated before repairing the generator, so the
    failure mode is checked rather than only described informally. *)
Theorem stable_kernel_bisim_silent_self_loop_r s2
    (Hloop : stable_kernel_silent_r s2 s2) :
  forall s1, stable_kernel_bisim s1 s2.
Proof.
  intro s1. revert s1. unfold stable_kernel_bisim.
  coinduction CH CIH. intro s1.
  unfold stable_kernel_bisim_body.
  eapply SKBSilentR; [exact Hloop|].
  apply CIH.
Qed.

Theorem stable_kernel_bisim_silent_self_loop_l s1
    (Hloop : stable_kernel_silent_l s1 s1) :
  forall s2, stable_kernel_bisim s1 s2.
Proof.
  intro s2. revert s2. unfold stable_kernel_bisim.
  coinduction CH CIH. intro s2.
  unfold stable_kernel_bisim_body.
  eapply SKBSilentL; [exact Hloop|].
  apply CIH.
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
