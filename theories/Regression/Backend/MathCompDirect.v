(** Gate M only. Never imported by the safe AllImports aggregate.
    Direct capability and program acceptance; not a universe-consistency claim.
    The checked negative counterparts remain in MathCompUniverse.v. *)
Set Warnings "-ambiguous-paths".
Local Unset Universe Checking.
Require PTree.Regression.Backend.FreeOmegaUpperContracts.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order reals boolp
  classical_sets measure ereal.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure NativeLaws OrderLaws OmegaLaws BindLaws Retry.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel PEutt.
From PTree.Eq.Backend.MathComp Require Import Direct.
From PTree.Examples Require Import MathCompPrograms.
From PTree.Eq Require Import Canonical.
Set Implicit Arguments.
Import GRing.Theory Num.Theory Order.Theory.

Section Probes.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation MX := (MathCompNativeMixedMeasure R).
Local Notation E := (fun _ : Type => Empty_set).

Definition direct_ret : ptree E M bool := Ret true.
Definition direct_frontier : Type := @mathcomp_direct_frontier R E bool.
Definition direct_kernel := @mathcomp_direct_kernel R E bool.
Definition direct_hitting := @mathcomp_direct_hitting R E bool.

(** Positive assembly probes consume the checked native instances. *)
Definition available_native_order : @SemanticMeasureOrderLaws M NI NO := _.
Definition available_native_omega : @SemanticOmegaLaws M NI NO := _.
Definition available_general_hitting_exists :=
  @ptree_stable_hitting_exists E M M NI MX NO _ _ bool.

Context `{G : MathCompCouplingGluing R}.
Example direct_canonical_profile {F A B} (RR : A -> B -> Prop)
    (t : ptree F M A) (u : ptree F M B) :
  canonical_peutt RR t u =
  @peutt F M M NI (@MathCompNodeSemanticMeasureCoreLaws R G)
    MX NO A B RR t u.
Proof. reflexivity. Qed.

Example direct_ret_reflexivity :
  @mathcomp_direct_peutt R G E bool direct_ret direct_ret.
Proof. apply mathcomp_direct_peutt_refl. Qed.

Example direct_eventful_reflexivity {F A} (t : ptree F M A) :
  @mathcomp_direct_peutt R G F A t t.
Proof. apply mathcomp_direct_peutt_refl. Qed.
End Probes.

Section Programs.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation MX := (MathCompNativeMixedMeasure R).
Context {E : Type -> Type} {A : Type}.
Variable q : R.
Hypothesis Hq : (0 < q <= 1)%R.
Variable value : A.
Local Notation retry := (@mathcomp_retry E A R (mathcomp_bernoulli q) value).
Local Notation hits := (@mathcomp_direct_hitting R E A).
Local Notation W := (@mathcomp_direct_peutt R G E A).

Lemma direct_retry_hitting : hits (observe retry) (sem_ret (FHRet value)).
Proof.
  destruct (mathcomp_direct_hitting_exists R retry) as [out Hout].
  assert (Htau : hits (observe (Tau retry)) out).
  { apply (proj2 (ptree_stable_hitting_tau_iff _ _)); exact Hout. }
  assert (Hprob : hits (observe retry)
    (sem_bind (mathcomp_bernoulli q)
      (fun b => if b then sem_ret (FHRet value) else out))).
  { rewrite mathcomp_retry_observe.
    eapply (ptree_stable_hitting_prob (MX := MX)) with (Good := fun _ => True).
    - apply mathcomp_kernel_ae_true.
    - intros [] _; [apply ptree_stable_hitting_ret|exact Htau]. }
  assert (He : mathcomp_kernel_eq out (sem_ret (FHRet value))).
  { apply (@mathcomp_retry_fixed_point R _ q out (sem_ret (FHRet value)) Hq).
    exact (ptree_stable_hitting_unique Hout Hprob). }
  exact (mathcomp_kernel_lub_limit_proper He Hout).
Qed.

Example direct_unbounded_retry : W retry (Ret value).
Proof.
  eapply peutt_of_hitting_lift.
  - exact direct_retry_hitting.
  - apply stable_hitting_ret.
  - apply mathcomp_kernel_lift_ret. constructor; reflexivity.
Qed.

Example direct_retry_before_vis {X} (e : E X)
    (k : X -> ptree E M A) :
  W (Vis e (fun x => Tau (k x))) (Vis e k).
Proof. apply peutt_vis; intros x; apply peutt_tau_l. Qed.

End Programs.

Section Composition.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation MX := (MathCompNativeMixedMeasure R).
Context {E : Type -> Type} {A : Type}.
Variables q p : R.
Hypotheses (Hq : (0 < q <= 1)%R) (Hp : (0 < p <= 1)%R).
Variable value : A.
Local Notation outer := (@mathcomp_retry E unit R (mathcomp_bernoulli q) tt).
Local Notation inner := (@mathcomp_retry E A R (mathcomp_bernoulli p) value).
Local Notation W := (@mathcomp_direct_peutt R G E A).

Example direct_eventful_bind_rewrite (k : unit -> ptree E M A) :
  W (PTree.bind outer k) (k tt).
Proof.
  change (W (PTree.bind outer k) (PTree.bind (Ret tt) k)).
  eapply mathcomp_direct_peutt_bind with (RR := eq).
  - apply direct_unbounded_retry; exact Hq.
  - intros x y ->; apply mathcomp_direct_peutt_refl.
Qed.

Example direct_nested_unbounded_retry :
  W (PTree.bind outer (fun _ => inner)) (Ret value).
Proof.
  eapply peutt_trans.
  - apply direct_eventful_bind_rewrite.
  - apply direct_unbounded_retry; exact Hp.
Qed.

(** Both approximation indices describe genuinely unbounded retries. This
    is the diagonal/Fubini route, not a finite maximum of inner stopping times. *)
Example direct_nested_retry_diagonal :
  @sem_lub M NI NO _
    (fun n => @ptree_bind_diagonal_approx E M M NI MX NO unit A n
      outer (fun _ => inner)) (sem_ret (FHRet value)).
Proof.
  pose front (_ : unit) : M (stable_head E M A) :=
    @sem_ret M NI _ (FHRet value).
  pose next := @stable_head_bind_front E M M NI unit A (fun _ => inner) front.
  apply (@mathcomp_kernel_lub_limit_proper R _ _
    (mathcomp_kernel_bind (sem_ret (FHRet tt)) next)).
  - apply mathcomp_kernel_bind_ret_l.
  - unfold ptree_bind_diagonal_approx.
    apply (sem_bind_diagonal_lub (S := M) (SI := NI) (SO := NO)).
    + apply ptree_hitting_increasing.
    + intro head; apply ptree_head_bind_approx_increasing.
    + exact (@direct_retry_hitting R G E unit q Hq tt).
    + intro head; apply ptree_head_bind_approx_lub.
      intro x; exact (@direct_retry_hitting R G E A p Hp value).
Qed.

Example direct_retry_vis_interaction {X} (e : E X)
    (k : X -> ptree E M A) :
  W (PTree.bind outer (fun _ => Vis e k)) (Vis e k).
Proof. apply direct_eventful_bind_rewrite. Qed.
End Composition.

(** Both relations and both result carriers are independent; this endpoint
    consumes the same generic theorem as FreeOmega, through native laws. *)
Section HeterogeneousBind.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Context {E : Type -> Type} {A B X Y : Type}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NC := (@MathCompNodeSemanticMeasureCoreLaws R G).
Local Notation MX := (MathCompNativeMixedMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation W := (@peutt E M M NI NC MX NO).

Example direct_heterogeneous_bind (RR : X -> Y -> Prop) (RS : A -> B -> Prop)
    (t : ptree E M X) (u : ptree E M Y)
    (k : X -> ptree E M A) (h : Y -> ptree E M B) :
  W RR t u -> (forall x y, RR x y -> W RS (k x) (h y)) ->
  W RS (PTree.bind t k) (PTree.bind u h).
Proof. apply mathcomp_direct_peutt_bind. Qed.
End HeterogeneousBind.

(** Direct assembly is still confined to this existing Gate M file. These
    clients consume generic Proper proofs, not MathComp copies. *)
From PTree.Eq Require Import Algebra.
From Coq Require Import Morphisms.
From PTree.Prob.Backend.MathComp Require Import BindOrder.
Section GenericRewriting.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Context {E : Type -> Type} {A B : Type}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NC := (@MathCompNodeSemanticMeasureCoreLaws R G).
Local Notation MX := (MathCompNativeMixedMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation W := (@peutt E M M NI NC MX NO).

Example direct_bind_setoid (t u : ptree E M A)
    (k : A -> ptree E M B) (H : W eq t u) :
  W eq (PTree.bind t k) (PTree.bind u k).
Proof.
  assert (Hp : Proper (W eq ==> pointwise_relation A (W eq) ==> W eq)
    (@PTree.bind E M A B)) by apply peutt_bind_Proper.
  Timeout 10 setoid_rewrite H. apply peutt_refl.
Qed.

Example direct_continuation_setoid (t : ptree E M A)
    (k h : A -> ptree E M B) (H : forall x, W eq (k x) (h x)) :
  W eq (PTree.bind t k) (PTree.bind t h).
Proof.
  assert (Hp : Proper (W eq ==> pointwise_relation A (W eq) ==> W eq)
    (@PTree.bind E M A B)) by apply peutt_bind_Proper.
  assert (Hpoint : pointwise_relation A (W eq) k h) by exact H.
  Timeout 10 setoid_rewrite Hpoint. apply peutt_refl.
Qed.

Example direct_fmap_setoid (f : A -> B) (t u : ptree E M A)
    (H : W eq t u) :
  W eq (PTree.fmap f t) (PTree.fmap f u).
Proof.
  assert (Hp : Proper (W eq ==> W eq) (PTree.fmap f)) by apply peutt_fmap_Proper.
  Timeout 10 setoid_rewrite H. apply peutt_refl.
Qed.
End GenericRewriting.

(** The exact same sampling equations work with MN = MF, without a
    FreeOmega completion or a relational-lub certificate. *)
Section GenericSampling.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Context {E : Type -> Type} {A B : Type}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NC := (@MathCompNodeSemanticMeasureCoreLaws R G).
Local Notation MX := (MathCompNativeMixedMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation W := (@peutt E M M NI NC MX NO).

Example direct_sample_bind (mu : M A) (k : A -> ptree E M B) :
  W eq (PTree.bind (Prob mu (fun x => Ret x)) k) (Prob mu k).
Proof. apply (peutt_sample_bind (NI := NI)). Qed.

Example direct_sample_map (mu : M A) (f : A -> B) :
  W eq (Prob mu (fun x => Ret (f x)))
    (Prob (sem_bind mu (fun x => sem_ret (f x))) (fun a => Ret a)).
Proof. apply (peutt_sample_map (NI := NI)). Qed.
End GenericSampling.

(** The eventful closure rule is independent of completion. The caller must
    still establish generator closure; this does not assert unrestricted
    behavioral iteration congruence. *)
From PTree.Eq Require Import Iter.
Section GenericIteration.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Context {E : Type -> Type} {I1 I2 A B : Type}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NC := (@MathCompNodeSemanticMeasureCoreLaws R G).
Local Notation MX := (MathCompNativeMixedMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Variable step1 : I1 -> ptree E M (I1 + A).
Variable step2 : I2 -> ptree E M (I2 + B).
Variable SI : I1 -> I2 -> Prop.
Variable RR : A -> B -> Prop.

Example direct_eventful_iter
    (H : @iter_eventful_generator_closed E M M NI MX NO I1 I2 A B
      step1 step2 SI RR) i j :
  SI i j -> @peutt E M M NI NC MX NO A B RR
    (PTree.iter step1 i) (PTree.iter step2 j).
Proof. intro Hij. exact (peutt_iter_eventful_of_generator_closed H Hij). Qed.
End GenericIteration.

(** Heterogeneous effect refinement, with a semantically checked guard.
    All scheduling and preservation proofs come from generic owners. *)
From PTree.Interp Require Import Kernel Scheduling Preservation Guarded.
From PTree.Prob.Interface Require Import AE Coupling.
Section GenericInterpretation.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Context {E F : Type -> Type}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NC := (@MathCompNodeSemanticMeasureCoreLaws R G).
Local Notation MX := (MathCompNativeMixedMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Variable rename : forall X, E X -> F X.

Definition direct_guarded_handler X (e : E X) : ptree F M X :=
  Tau (Vis (rename e) (fun x => Ret x)).

Lemma direct_handler_guarded :
  @guarded_handler E F M M NI MX NO direct_guarded_handler.
Proof.
  apply PTree.Interp.Guarded.guarded_handler_of_hitting.
  intros X e. exists (sem_ret (FHVis (rename e) (fun x => Ret x))). split.
  - apply (proj2 (ptree_stable_hitting_tau_iff (FI := NI) (FO := NO) _ _)).
    apply stable_hitting_vis.
  - apply sem_ae_ret. exact I.
Qed.

Example direct_guarded_interp {A B} (RR : A -> B -> Prop)
    (t : ptree E M A) (u : ptree E M B) :
  @peutt E M M NI NC MX NO A B RR t u ->
  @peutt F M M NI NC MX NO A B RR
    (PTree.interp direct_guarded_handler t)
    (PTree.interp direct_guarded_handler u).
Proof. apply PTree.Interp.Guarded.peutt_interp_guarded. exact direct_handler_guarded. Qed.

Example direct_guarded_tau {A} (t : ptree E M A) :
  @peutt F M M NI NC MX NO A A eq
    (PTree.interp direct_guarded_handler (Tau t))
    (PTree.interp direct_guarded_handler t).
Proof. apply direct_guarded_interp. apply peutt_tau_l. Qed.
End GenericInterpretation.

(** Same generic structural consumers. The native relational-limit theorem
    is still open, so complete-limit endpoints explicitly retain Hlimit.
    Finite approximants need no such premise. No new unsafe file is added. *)
From PTree.Prob.Interface Require Import RelationalClosure.
From PTree.Prob.Backend.MathComp Require Import RelationalClosure.
From PTree.Eq Require Import Relation PStruct PStrong.
Section RelationalConsumers.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Context {E : Type -> Type}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NC := (@MathCompNodeSemanticMeasureCoreLaws R G).
Local Notation MX := (MathCompNativeMixedMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).

Example direct_finite_strong {A B} (RR : A -> B -> Prop)
    (t : ptree E M A) (u : ptree E M B) n :
  @pstrong E M NI NC A B RR t u ->
  @sem_lift M NI _ _ (stable_head_rel RR (@pstrong E M NI NC A B RR))
    (@ptree_hitting_approx E M M NI MX NO A n (observe t))
    (@ptree_hitting_approx E M M NI MX NO B n (observe u)).
Proof.
  apply (PTree.Eq.Relation.ptree_hitting_pstrong (@mathcomp_relational_bind R)
    (@mathcomp_relational_mixed_bind R) (@mathcomp_relational_zero R)).
Qed.

Variable Hlimit : relational_lub NO.

Example direct_structural_bridge_of_relational_lub {A B} (RR : A -> B -> Prop)
    (t : ptree E M A) (u : ptree E M B) :
  pstruct RR t u -> @peutt E M M NI NC MX NO A B RR t u.
Proof.
  apply (PTree.Eq.Relation.peutt_of_pstruct (@mathcomp_relational_bind R)
    (@mathcomp_relational_mixed_bind R) (@mathcomp_relational_zero R) Hlimit).
Qed.

Example direct_codiagonal_of_relational_lub {I A}
    (step : I -> ptree E M (I + (I + A))) i :
  @peutt E M M NI NC MX NO A A eq
    (PTree.iter (fun j => PTree.iter step j) i)
    (PTree.iter (pstruct_iter_codiagonal_flat_step step) i).
Proof.
  apply (PTree.Eq.Iter.peutt_iter_codiagonal (@mathcomp_relational_bind R)
    (@mathcomp_relational_mixed_bind R) (@mathcomp_relational_zero R) Hlimit).
Qed.
End RelationalConsumers.

(** Eventful behavioral congruence, not the entry-only closure rule above.
    Only direct assembly is unchecked. Gluing and relational-lub remain
    explicit mathematical premises; no claim that they are discharged. *)
From PTree.Interp Require Import Iteration.
Section BehavioralIteration.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Context {E : Type -> Type} {I J A B : Type}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NC := (@MathCompNodeSemanticMeasureCoreLaws R G).
Local Notation MX := (MathCompNativeMixedMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Variable Hlimit : relational_lub NO.

Example direct_behavioral_iter_of_relational_lub
    (step1 : I -> ptree E M (I+A)) (step2 : J -> ptree E M (J+B))
    (SI : I -> J -> Prop) (RR : A -> B -> Prop) :
  (forall i j, SI i j -> @peutt E M M NI NC MX NO (I+A) (J+B)
    (pstruct_iter_sum_rel SI RR) (step1 i) (step2 j)) ->
  forall i j, SI i j -> @peutt E M M NI NC MX NO A B RR
    (PTree.iter step1 i) (PTree.iter step2 j).
Proof.
  apply (peutt_iter_eventful_rel (@mathcomp_relational_mixed_bind R)
    (@mathcomp_relational_zero R) Hlimit).
Qed.
End BehavioralIteration.

(** Explicit monad laws and pure-map uniformity, still conditional on native
    relational-lub closure and confined to this existing direct client. *)
From ITree.Basics Require Import Basics Monad.
From PTree.Core Require Import IterationLaws.
From PTree.Interp Require Import IterationAlgebra.
Section BehavioralIterationAlgebra.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Context {E : Type -> Type}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation Q := (ptree_peutt_eq1 (E := E) (FI := NI)).
Variable Hlimit : relational_lub NO.

Example direct_monad_laws_of_relational_lub :
  @MonadLawsE (ptree E M) Q Monad_ptree.
Proof.
  exact (ptree_peutt_monad_laws (@mathcomp_relational_mixed_bind R)
    (@mathcomp_relational_zero R) Hlimit).
Qed.

Example direct_uniformity_of_relational_lub {I J A}
    (f : I -> ptree E M (I+A)) (g : J -> ptree E M (J+A)) (h : I -> J) :
  (forall i, @eq1 _ Q _
    (PTree.bind (f i) (fun v => Ret (iteration_map h v))) (g (h i))) ->
  forall i, @eq1 _ Q _ (PTree.iter f i) (PTree.iter g (h i)).
Proof.
  apply (peutt_iter_uniform (@mathcomp_relational_mixed_bind R)
    (@mathcomp_relational_zero R) Hlimit).
Qed.
End BehavioralIterationAlgebra.

(** Full Eq1-wide uniformity from the direct machine, not the protocol
    proof. Mathematical premises and the existing Gate M boundary remain. *)
From PTree.Interp Require Import IterationUniform.
Section FullIterationUniformity.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Context {E : Type -> Type}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Variable Hlimit : relational_lub NO.

Example direct_full_uniformity_of_relational_lub :
  @iteration_uniform (ptree E M) Monad_ptree MonadIter_ptree
    (ptree_peutt_eq1 (FI := NI)).
Proof.
  exact (ptree_peutt_iteration_uniform (@mathcomp_relational_mixed_bind R)
    (@mathcomp_relational_zero R) Hlimit).
Qed.

Example direct_iter_Proper_of_relational_lub {I A} :
  Proper
    (pointwise_relation I (peutt (FI := NI) eq) ==>
     eq ==> peutt (E := E) (FI := NI) eq)
    (@PTree.iter E M A I).
Proof. exact (peutt_iter_Proper (@mathcomp_relational_zero R) Hlimit). Qed.
End FullIterationUniformity.

(** The SAME generic MDP/atomic theorems at MN = MF. These clients add no
    unchecked probability mathematics. Gluing remains explicit; total-map is
    discharged by the universe-checked native returned-mass theorem. *)
From PTree.Interp Require Import MDP Atomic MDPAtomic.
From PTree.Semantics Require Import MDPFragment TreeTransitionBisim.
Section GenericMDPClients.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Context {E F : Type -> Type} {A : Type}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NC := (@MathCompNodeSemanticMeasureCoreLaws R G).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation MX := (MathCompNativeMixedMeasure R).
Variable h : forall X, E X -> ptree F M X.

Example direct_mdp_interp (Hh : MDP.mdp_handler (FI := NI) (MX := MX) (FO := NO) (R := A) h)
    (t : ptree E M A) :
  @mdp_state E M M NI NC MX NO A t ->
  @mdp_state F M M NI NC MX NO A (PTree.interp h t).
Proof. exact (MDP.mdp_state_interp (FI := NI) (FO := NO) (MX := MX) Hh (t := t)). Qed.

Example direct_mdp_guarded_transition
    (Hh : MDP.mdp_handler (FI := NI) (MX := MX) (FO := NO) (R := A) h)
    (Hg : PTree.Interp.Guarded.guarded_handler (FI := NI) (MX := MX) (FO := NO) h)
    (t u : ptree E M A) :
  @mdp_state E M M NI NC MX NO A t ->
  @mdp_state E M M NI NC MX NO A u ->
  @tree_trans_bisim E M M NI NC MX NO A A eq t u ->
  @tree_trans_bisim F M M NI NC MX NO A A eq (PTree.interp h t) (PTree.interp h u).
Proof.
  exact (MDP.mdp_guarded_interp_tree_trans (FI := NI) (FO := NO) (MX := MX)
    Hh Hg (t := t) (u := u)).
Qed.

Variable a : forall X, E X -> ptree E M X.
Variable atom : Atomic.atomic_handler (FI := NI) (MX := MX) (FO := NO) a.
Example direct_atomic_transition (RR : A -> A -> Prop) (t u : ptree E M A) :
  @tree_trans_bisim E M M NI NC MX NO A A RR t u ->
  @tree_trans_bisim E M M NI NC MX NO A A RR (PTree.interp a t) (PTree.interp a u).
Proof.
  exact (Atomic.tree_trans_bisim_interp_atomic (FI := NI) (FO := NO) (MX := MX)
    (@mathcomp_kernel_bind_ret_r R) (@mathcomp_kernel_lub_limit_proper R)
    atom (RR := RR) (t := t) (u := u)).
Qed.

Example direct_atomic_mdp
    (t : ptree E M A) :
  @mdp_state E M M NI NC MX NO A t ->
  @mdp_state E M M NI NC MX NO A (PTree.interp a t).
Proof.
  apply (MDPAtomic.mdp_state_interp_atomic (FI := NI) (FO := NO) (MX := MX)
    (@mathcomp_kernel_lub_limit_proper R) (atom := atom)).
  intros mu Hmu. exact (proj2 (mathcomp_kernel_map_total _ _) Hmu).
Qed.
End GenericMDPClients.

(** Left unit is shallow: unlike structural bridge/iteration clients above,
    this theorem needs no unresolved relational-limit certificate. *)
Section ShallowDirectClient.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Context {E : Type -> Type} {A B : Type}.
Example direct_left_unit_without_relational_lub (a : A)
    (k : A -> ptree E (MathCompKernelMeasure R) B) :
  @mathcomp_direct_peutt R G E B (PTree.bind (Ret a) k) (k a).
Proof. apply PTree.Eq.Algebra.peutt_bind_ret_l. Qed.
End ShallowDirectClient.

(** Classical MDP correspondence uses the existing generic proof in both
    directions. No relational-lub premise, external validation model, or
    native/frontier reflection assumption remains: native map reflection is
    proved in Gate S. Gluing and the Gate M universe boundary remain explicit. *)
From PTree.Semantics Require Import MDPEmbedding MDPReflection HeadTransition.
From PTree.Prob.Interface Require Import AE.
Section DirectMDPCorrespondence.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NC := (@MathCompNodeSemanticMeasureCoreLaws R G).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation MX := (MathCompNativeMixedMeasure R).
Variable D : MDP M.
Local Notation E := (mdpE (mdp_observations D) (mdp_actions D)).
Local Notation encode := (mdp_encode (D := D)).
Local Notation ehead := (mdp_encode_head (D := D)).

Lemma direct_mdp_successors_total s a :
  @sem_total M NI NO _
    (mdp_successors (FI := NI) (MX := MX) (D := D) (mdp_transition D s a)).
Proof.
  apply (proj2 (mathcomp_kernel_map_total _ _)).
  exact (@mdp_transition_total M NI NO D s a).
Qed.

Lemma direct_mdp_successors_support s a :
  @sem_ae M NI _
    (mdp_successors (FI := NI) (MX := MX) (D := D) (mdp_transition D s a))
    (fun h => exists t, h = ehead t).
Proof.
  unfold mdp_successors. change (sem_ae
    (sem_bind (mdp_transition D s a) (fun t => sem_ret (ehead t)))
    (fun h => exists t, h = ehead t)).
  eapply sem_ae_bind with (P := fun _ => True); [apply sem_ae_true|].
  intros t _. apply sem_ae_ret. exists t. reflexivity.
Qed.

Example direct_encode_mdp_state s :
  @mdp_state E M M NI NC MX NO unit (encode s).
Proof.
  apply (mdp_encode_mdp_state (FI := NI) (FO := NO));
    [apply direct_mdp_successors_total|apply direct_mdp_successors_support].
Qed.

Example direct_mdp_step_iff s a out :
  @head_step E M M NI MX NO unit (ehead s)
    (Obs (Choose (mdp_observe D s)) a) out <->
  @sem_eq M NI _ out
    (mdp_successors (FI := NI) (MX := MX) (D := D) (mdp_transition D s a)).
Proof.
  apply (mdp_encode_step_iff (FI := NI) (FO := NO)
    (@mathcomp_kernel_lub_limit_proper R)).
Qed.

Example direct_mdp_head_bisim_iff s t :
  mdp_bisim (D := D) s t <->
  @head_bisim E M M NI NC MX NO unit unit eq (ehead s) (ehead t).
Proof.
  apply (mdp_head_bisim_iff (NI := NI) (NO := NO) (FI := NI) (FO := NO) (MX := MX)
    (@mathcomp_kernel_map_reflect R G)).
Qed.

Example direct_mdp_peutt_iff s t :
  mdp_bisim (D := D) s t <->
  @peutt E M M NI NC MX NO unit unit eq (encode s) (encode t).
Proof.
  apply (mdp_peutt_iff (NI := NI) (NO := NO) (FI := NI) (FO := NO) (MX := MX)
    (@mathcomp_kernel_map_reflect R G)).
Qed.

Example direct_mdp_tree_trans_bisim_iff s t :
  mdp_bisim (D := D) s t <->
  @tree_trans_bisim E M M NI NC MX NO unit unit eq (encode s) (encode t).
Proof.
  apply (mdp_tree_trans_bisim_iff (NI := NI) (NO := NO) (FI := NI) (FO := NO) (MX := MX)
    (FOAE := MathCompNativeOmegaAELaws R)
    (@mathcomp_kernel_map_reflect R G));
    [apply direct_mdp_successors_total|apply direct_mdp_successors_support].
Qed.
End DirectMDPCorrespondence.
