Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Program.
From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier UnifiedPWeak.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Targets of the genuinely operational state-to-distribution kernel.
    Stable observations stop the internal computation; internal targets are
    PTree states from which the kernel can take another step. *)
Polymorphic Variant operational_target
    (E : Type -> Type) (MN : Type -> Type) (R : Type) : Type :=
  | OPStable (h : frontier_head E MN R)
  | OPInternal (t : ptree E MN R).

Arguments OPStable {E MN R} _.
Arguments OPInternal {E MN R} _.

Section OperationalKernel.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

(** One primitive PTree step, interpreted directly as a behavior-layer
    distribution.  The only syntax inspection in the operational semantics
    is here.  In particular, no rule recognizes [PTree.iter], [PTree.bind],
    or nested iteration. *)
Definition operational_kernel {R} (ot : ptree' E MN R) :
    MF (operational_target E MN R) :=
  match ot with
  | RetF r => sem_ret (OPStable (FHRet r))
  | VisF _ e k => sem_ret (OPStable (FHVis e k))
  | TauF t => sem_ret (OPInternal t)
  | ProbF _ mu k =>
      mixed_bind mu (fun x => sem_ret (OPInternal (k x)))
  end.

(** The same primitive transition in the generic stable-hitting interface.
    Residual states are observations, not syntax constructors: taking the
    transition never recognizes a derived [bind] or [iter] form. *)
Definition ptree_primitive_kernel {R} (ot : ptree' E MN R) :
    MF (stable_target (ptree' E MN R) (frontier_head E MN R)) :=
  match ot with
  | RetF r => sem_ret (SHStable (FHRet r))
  | VisF _ e k => sem_ret (SHStable (FHVis e k))
  | TauF t => sem_ret (SHInternal (observe t))
  | ProbF _ mu k =>
      mixed_bind mu (fun x => sem_ret (SHInternal (observe (k x))))
  end.

(** Resolve one operational target using at most [fuel] further primitive
    steps.  Unresolved internal mass goes to [sem_zero]. *)
Fixpoint operational_target_approx {R} (fuel : nat)
    (target : operational_target E MN R) :
    MF (frontier_head E MN R) :=
  match target with
  | OPStable h => sem_ret h
  | OPInternal t =>
      match fuel with
      | O => sem_zero
      | Datatypes.S fuel' =>
          sem_bind (operational_kernel (observe t))
            (operational_target_approx fuel')
      end
  end.

(** The [fuel]-bounded stable-hitting distribution of an observed state.
    Fuel counts primitive internal transitions.  Ret and Vis are stable after
    their one primitive observation step; Tau and Prob recursively spend the
    remaining fuel through the same kernel. *)
Definition operational_hitting_approx {R} (fuel : nat)
    (ot : ptree' E MN R) : MF (frontier_head E MN R) :=
  sem_bind (operational_kernel ot) (operational_target_approx fuel).

(** A generic weak behavior is the (possibly subprobabilistic) stable-hitting
    limit of primitive execution.  Unresolved mass is absent from each finite
    approximant, hence pure divergence has the zero subdistribution as its
    hitting limit. *)
Definition operational_weak {R} (ot : ptree' E MN R)
    (out : MF (frontier_head E MN R)) : Prop :=
  sem_lub (fun fuel => operational_hitting_approx fuel ot) out.

(** AST is a separate property of a weak behavior: its stable-hitting limit
    has total mass.  Keeping these notions separate is necessary because an
    ordinary finite frontier may legitimately be a subprobability measure. *)
Definition operational_ast_weak {R} (ot : ptree' E MN R)
    (out : MF (frontier_head E MN R)) : Prop :=
  operational_weak ot out /\ sem_total out.

(** A syntax-independent bridge for genuinely nested unbounded execution.
    [grid outer inner] may allocate separate fuel to an outer protocol and
    an inner AST sampler.  The program-specific obligation is only that its
    primitive global-fuel chain has the same limits as the diagonal grid.
    Fubini continuity then turns iterated row limits into that diagonal
    limit; no [Bind], [Iter], or [NestedIter] semantic constructor is used. *)
Definition operational_hitting_diagonal_cofinal {R}
    (ot : ptree' E MN R)
    (grid : nat -> nat -> MF (frontier_head E MN R)) : Prop :=
  forall out,
    sem_lub (fun fuel => operational_hitting_approx fuel ot) out <->
    sem_lub (fun fuel => grid fuel fuel) out.

Section OperationalNestedGrid.
Context `{FFubini : @SemanticOmegaFubiniLaws MF FI FO}.

Theorem operational_weak_of_nested_grid {R}
    (ot : ptree' E MN R)
    (grid : nat -> nat -> MF (frontier_head E MN R))
    (row_out : nat -> MF (frontier_head E MN R)) out :
  operational_hitting_diagonal_cofinal ot grid ->
  (forall outer, sem_increasing (grid outer)) ->
  (forall inner, sem_increasing (fun outer => grid outer inner)) ->
  (forall outer, sem_lub (grid outer) (row_out outer)) ->
  sem_lub row_out out ->
  operational_weak ot out.
Proof.
  intros Hcofinal Hinner Houter Hrows Hout.
  unfold operational_weak.
  apply (proj2 (Hcofinal out)).
  eapply sem_lub_double_diagonal; eassumption.
Qed.

Corollary operational_ast_weak_of_nested_grid {R}
    (ot : ptree' E MN R)
    (grid : nat -> nat -> MF (frontier_head E MN R))
    (row_out : nat -> MF (frontier_head E MN R)) out :
  operational_hitting_diagonal_cofinal ot grid ->
  (forall outer, sem_increasing (grid outer)) ->
  (forall inner, sem_increasing (fun outer => grid outer inner)) ->
  (forall outer, sem_lub (grid outer) (row_out outer)) ->
  sem_lub row_out out ->
  sem_total out ->
  operational_ast_weak ot out.
Proof.
  intros Hcofinal Hinner Houter Hrows Hout Htotal.
  split; [|exact Htotal].
  eapply operational_weak_of_nested_grid; eassumption.
Qed.

End OperationalNestedGrid.

Lemma operational_kernel_retE {R} (r : R) :
  operational_kernel (RetF r) =
  sem_ret (OPStable (FHRet r)).
Proof. reflexivity. Qed.

Lemma operational_kernel_visE {R X} (e : E X)
    (k : X -> ptree E MN R) :
  operational_kernel (VisF e k) =
  sem_ret (OPStable (FHVis e k)).
Proof. reflexivity. Qed.

Lemma operational_kernel_tauE {R} (t : ptree E MN R) :
  operational_kernel (TauF t) = sem_ret (OPInternal t).
Proof. reflexivity. Qed.

Lemma operational_kernel_probE {R X} (mu : MN X)
    (k : X -> ptree E MN R) :
  operational_kernel (ProbF mu k) =
  mixed_bind mu (fun x => sem_ret (OPInternal (k x))).
Proof. reflexivity. Qed.

Lemma operational_target_stableE {R} fuel
    (h : frontier_head E MN R) :
  operational_target_approx fuel (OPStable h) = sem_ret h.
Proof. destruct fuel; reflexivity. Qed.

Lemma operational_target_internal_zeroE {R} (t : ptree E MN R) :
  operational_target_approx O (OPInternal t) = sem_zero.
Proof. reflexivity. Qed.

Lemma operational_target_internal_succE {R} fuel
    (t : ptree E MN R) :
  operational_target_approx (Datatypes.S fuel)
    (OPInternal t) =
  sem_bind (operational_kernel (observe t))
    (operational_target_approx fuel).
Proof. reflexivity. Qed.

End OperationalKernel.

Section OperationalKernelLaws.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}.

(** These equations are derived from the single operational kernel.  They
    are not constructors of the weak semantics. *)
Lemma operational_hitting_ret {R} fuel (r : R) :
  sem_eq (operational_hitting_approx (MF := MF) fuel (RetF r))
    (sem_ret (FHRet r : frontier_head E MN R)).
Proof.
  unfold operational_hitting_approx. rewrite operational_kernel_retE.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite operational_target_stableE. apply sem_eq_refl.
Qed.

Lemma operational_hitting_vis {R X} fuel (e : E X)
    (k : X -> ptree E MN R) :
  sem_eq (operational_hitting_approx (MF := MF) fuel (VisF e k))
    (sem_ret (FHVis e k : frontier_head E MN R)).
Proof.
  unfold operational_hitting_approx. rewrite operational_kernel_visE.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite operational_target_stableE. apply sem_eq_refl.
Qed.

Lemma operational_hitting_tau_zero {R} (t : ptree E MN R) :
  sem_eq (operational_hitting_approx (MF := MF) O (TauF t)) sem_zero.
Proof.
  unfold operational_hitting_approx. rewrite operational_kernel_tauE.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite operational_target_internal_zeroE. apply sem_eq_refl.
Qed.

Lemma operational_hitting_tau_succ {R} fuel (t : ptree E MN R) :
  sem_eq
    (operational_hitting_approx (MF := MF) (Datatypes.S fuel) (TauF t))
    (operational_hitting_approx fuel (observe t)).
Proof.
  unfold operational_hitting_approx at 1. rewrite operational_kernel_tauE.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite operational_target_internal_succE. apply sem_eq_refl.
Qed.

Lemma operational_hitting_prob {R X} fuel (mu : MN X)
    (k : X -> ptree E MN R) :
  sem_eq (operational_hitting_approx (MF := MF) fuel (ProbF mu k))
    (mixed_bind mu (fun x =>
      operational_target_approx fuel (OPInternal (k x)))).
Proof.
  unfold operational_hitting_approx. rewrite operational_kernel_probE.
  eapply sem_eq_trans.
  - apply mixed_bind_assoc.
  - apply mixed_bind_ae_proper.
    eapply sem_ae_mono; [|apply sem_ae_true].
    intros x _. apply sem_bind_ret_l.
Qed.

Lemma operational_hitting_prob_zero {R X} (mu : MN X)
    (k : X -> ptree E MN R) :
  sem_eq (operational_hitting_approx (MF := MF) O (ProbF mu k))
    (mixed_bind mu (fun _ => sem_zero)).
Proof.
  eapply sem_eq_trans; [apply operational_hitting_prob|].
  apply mixed_bind_ae_proper.
  eapply sem_ae_mono; [|apply sem_ae_true].
  intros x _. rewrite operational_target_internal_zeroE. apply sem_eq_refl.
Qed.

Lemma operational_hitting_prob_succ {R X} fuel (mu : MN X)
    (k : X -> ptree E MN R) :
  sem_eq
    (operational_hitting_approx (MF := MF) (Datatypes.S fuel) (ProbF mu k))
    (mixed_bind mu (fun x =>
      operational_hitting_approx fuel (observe (k x)))).
Proof.
  eapply sem_eq_trans; [apply operational_hitting_prob|].
  apply mixed_bind_ae_proper.
  eapply sem_ae_mono; [|apply sem_ae_true].
  intros x _. rewrite operational_target_internal_succE. apply sem_eq_refl.
Qed.

End OperationalKernelLaws.

Section GenericKernelAdequacy.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}.

(** Adequacy of the PTree adapter for the syntax-independent primitive
    kernel semantics.  This is pointwise in finite fuel, so the later weak
    and AST correspondence does not assume omega-limit uniqueness or a
    structured frontier derivation. *)
Theorem ptree_primitive_hitting_adequate {R} fuel
    (ot : ptree' E MN R) :
  sem_eq
    (stable_hitting_approx
      (@ptree_primitive_kernel E MN MF FI MX R) fuel ot)
    (operational_hitting_approx (MF := MF) fuel ot).
Proof.
  induction fuel as [|fuel IH] in ot |- *; destruct ot as [r|t|X e k|X mu k].
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_stableE.
    apply sem_eq_sym. apply operational_hitting_ret.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_internal_zeroE.
    apply sem_eq_sym. apply operational_hitting_tau_zero.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_stableE.
    apply sem_eq_sym. apply operational_hitting_vis.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply mixed_bind_assoc|].
    eapply sem_eq_trans.
    + apply mixed_bind_ae_proper.
      eapply sem_ae_mono; [|apply sem_ae_true].
      intros x _. eapply sem_eq_trans; [apply sem_bind_ret_l|].
      rewrite stable_target_internal_zeroE. apply sem_eq_refl.
    + apply sem_eq_sym. apply operational_hitting_prob_zero.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_stableE.
    apply sem_eq_sym. apply operational_hitting_ret.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_internal_succE.
    eapply sem_eq_trans; [apply IH|].
    apply sem_eq_sym. apply operational_hitting_tau_succ.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_stableE.
    apply sem_eq_sym. apply operational_hitting_vis.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply mixed_bind_assoc|].
    eapply sem_eq_trans.
    + apply mixed_bind_ae_proper.
      eapply sem_ae_mono; [|apply sem_ae_true].
      intros x _. eapply sem_eq_trans; [apply sem_bind_ret_l|].
      rewrite stable_target_internal_succE. apply IH.
    + apply sem_eq_sym. apply operational_hitting_prob_succ.
Qed.

Context `{FOL : @SemanticOmegaLaws MF FI FO}.

Theorem ptree_primitive_weak_adequate {R}
    (ot : ptree' E MN R) out :
  stable_hitting_weak
      (@ptree_primitive_kernel E MN MF FI MX R) ot out <->
  operational_weak (MF := MF) ot out.
Proof.
  unfold stable_hitting_weak, operational_weak. split; intro Hlim.
  - eapply sem_lub_chain_proper; [|exact Hlim].
    intro fuel. apply ptree_primitive_hitting_adequate.
  - eapply sem_lub_chain_proper; [|exact Hlim].
    intro fuel. apply sem_eq_sym.
    apply ptree_primitive_hitting_adequate.
Qed.

Theorem ptree_primitive_ast_adequate {R}
    (ot : ptree' E MN R) out :
  stable_hitting_ast
      (@ptree_primitive_kernel E MN MF FI MX R) ot out <->
  operational_ast_weak (MF := MF) ot out.
Proof.
  unfold stable_hitting_ast, operational_ast_weak.
  rewrite ptree_primitive_weak_adequate. reflexivity.
Qed.

End GenericKernelAdequacy.

Section GenericPTreeBisimulation.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Definition ptree_state_kernel {R} (ot : ptree' E MN R) :
    MF (stable_target (ptree' E MN R) (frontier_head E MN R)) :=
  @ptree_primitive_kernel E MN MF FI MX R ot.

Definition ptree_stable_observation_rel
    (sim : ptree' E MN R1 -> ptree' E MN R2 -> Prop) :
    frontier_head E MN R1 -> frontier_head E MN R2 -> Prop :=
  frontier_head_rel RR (fun t1 t2 => sim (observe t1) (observe t2)).

Lemma ptree_stable_observation_rel_mono sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall h1 h2,
    ptree_stable_observation_rel sim1 h1 h2 ->
    ptree_stable_observation_rel sim2 h1 h2.
Proof.
  intro Hsim. apply frontier_head_rel_mono.
  intros t1 t2 Hrel. exact (Hsim _ _ Hrel).
Qed.

(** Public PTree instance of the syntax-independent guarded kernel
    bisimulation.  All PTree syntax is confined to [ptree_state_kernel]; the
    greatest fixed point itself is the generic one. *)
Definition primitive_ptree_state_bisim :
    ptree' E MN R1 -> ptree' E MN R2 -> Prop :=
  @stable_kernel_bisim MF FI FC FO
    (ptree' E MN R1) (ptree' E MN R2)
    (frontier_head E MN R1) (frontier_head E MN R2)
    (@ptree_state_kernel R1) (@ptree_state_kernel R2)
    ptree_stable_observation_rel
    ptree_stable_observation_rel_mono.

Definition primitive_ptree_bisim
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) : Prop :=
  primitive_ptree_state_bisim (observe t1) (observe t2).

Lemma primitive_ptree_bisim_of_ast_lift
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) out1 out2 :
  operational_ast_weak (MF := MF) (observe t1) out1 ->
  operational_ast_weak (MF := MF) (observe t2) out2 ->
  sem_lift (frontier_head_rel RR primitive_ptree_bisim) out1 out2 ->
  primitive_ptree_bisim t1 t2.
Proof.
  intros H1 H2 Hlift. unfold primitive_ptree_bisim,
    primitive_ptree_state_bisim.
  pose proof (proj2 (ptree_primitive_ast_adequate
    (observe t1) out1) H1) as Hast1.
  pose proof (proj2 (ptree_primitive_ast_adequate
    (observe t2) out2) H2) as Hast2.
  apply stable_kernel_bisim_fold. eapply SKBAST.
  - split.
    + intros out1' Hast1'. exists out2. split; [exact Hast2|].
      eapply sem_lift_proper_l; [|exact Hlift].
      eapply sem_lub_unique; [exact (proj1 Hast1)|exact (proj1 Hast1')].
    + intros out2' Hast2'. exists out1. split; [exact Hast1|].
      eapply sem_lift_proper_r; [|exact Hlift].
      eapply sem_lub_unique; [exact (proj1 Hast2)|exact (proj1 Hast2')].
  - exact Hast1.
  - exact Hast2.
  - exact Hlift.
Qed.

Lemma ptree_stable_observation_rel_converse
    (sim : ptree' E MN R1 -> ptree' E MN R2 -> Prop) :
  forall h1 h2,
    ptree_stable_observation_rel sim h1 h2 ->
    @frontier_head_rel E MN R2 R1 (fun r2 r1 => RR r1 r2)
      (fun t2 t1 => sim (observe t1) (observe t2)) h2 h1.
Proof.
  intros h1 h2 Hrel. inversion Hrel; subst.
  - constructor. exact H.
  - constructor. intro x. exact (H x).
Qed.

End GenericPTreeBisimulation.

Section PrimitivePTreeBisimulationConverse.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Theorem primitive_ptree_bisim_converse : forall t1 t2,
  @primitive_ptree_bisim E MN MF FI FC MX FO R1 R2 RR t1 t2 ->
  @primitive_ptree_bisim E MN MF FI FC MX FO R2 R1
    (fun r2 r1 => RR r1 r2) t2 t1.
Proof.
  intros t1 t2 Hrel. unfold primitive_ptree_bisim,
    primitive_ptree_state_bisim in Hrel |- *.
  eapply stable_kernel_bisim_converse; [|exact Hrel].
  intros sim h1 h2 Hhead.
  exact (@ptree_stable_observation_rel_converse E MN R1 R2 RR
    sim h1 h2 Hhead).
Qed.

End PrimitivePTreeBisimulationConverse.

Section PrimitivePTreeBisimulationResultMonotonicity.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {R1 R2 : Type}.

Theorem primitive_ptree_bisim_rel_mono
    (RR1 RR2 : R1 -> R2 -> Prop)
    (HR : forall r1 r2, RR1 r1 r2 -> RR2 r1 r2) :
  forall t1 t2,
    @primitive_ptree_bisim E MN MF FI FC MX FO R1 R2 RR1 t1 t2 ->
    @primitive_ptree_bisim E MN MF FI FC MX FO R1 R2 RR2 t1 t2.
Proof.
  intros t1 t2 Hrel. unfold primitive_ptree_bisim,
    primitive_ptree_state_bisim in Hrel |- *.
  eapply stable_kernel_bisim_observation_mono; [|exact Hrel].
  intros sim1 sim2 Hsim h1 h2 Hhead. inversion Hhead; subst.
  - constructor. exact (HR _ _ H).
  - constructor. intro x. exact (Hsim _ _ (H x)).
Qed.

End PrimitivePTreeBisimulationResultMonotonicity.

Section PrimitivePTreeBisimulationSymmetry.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {R : Type}.

Theorem primitive_ptree_bisim_sym :
  Symmetric (@primitive_ptree_bisim E MN MF FI FC MX FO R R eq).
Proof.
  intros t1 t2 Hrel.
  eapply primitive_ptree_bisim_rel_mono.
  - intros r1 r2 Heq. symmetry. exact Heq.
  - exact (primitive_ptree_bisim_converse Hrel).
Qed.

End PrimitivePTreeBisimulationSymmetry.

Section PrimitivePTreeBisimulationTransitivity.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {R : Type}.

Lemma ptree_stable_observation_rel_comp
    (sim12 sim23 sim13 : ptree' E MN R -> ptree' E MN R -> Prop)
    (Hsim : forall s1 s3, (exists s2, sim12 s1 s2 /\ sim23 s2 s3) ->
      sim13 s1 s3) :
  forall h1 h3,
    (exists h2,
      @ptree_stable_observation_rel E MN R R eq sim12 h1 h2 /\
      @ptree_stable_observation_rel E MN R R eq sim23 h2 h3) ->
    @ptree_stable_observation_rel E MN R R eq sim13 h1 h3.
Proof.
  intros h1 h3 [h2 [H12 H23]].
  dependent destruction H12; dependent destruction H23.
  - constructor. reflexivity.
  - constructor. intro x. apply Hsim.
    exists (observe (k2 x)). split; [exact (H x)|exact (H0 x)].
Qed.

Theorem primitive_ptree_state_bisim_trans :
  Transitive (@primitive_ptree_state_bisim E MN MF FI FC MX FO R R eq).
Proof.
  intros s1 s2 s3 H12 H23.
  unfold primitive_ptree_state_bisim in H12, H23 |- *.
  eapply stable_kernel_bisim_compose; [|exact H12|exact H23].
  intros sim12 sim23 sim13 Hsim h1 h3 Hheads.
  exact (ptree_stable_observation_rel_comp Hsim Hheads).
Qed.

Theorem primitive_ptree_bisim_trans :
  Transitive (@primitive_ptree_bisim E MN MF FI FC MX FO R R eq).
Proof.
  intros t1 t2 t3 H12 H23.
  unfold primitive_ptree_bisim in H12, H23 |- *.
  eapply primitive_ptree_state_bisim_trans; eassumption.
Qed.

#[global] Instance primitive_ptree_bisim_equivalence :
  Equivalence (@primitive_ptree_bisim E MN MF FI FC MX FO R R eq).
Proof.
  split.
  - unfold Reflexive, primitive_ptree_bisim, primitive_ptree_state_bisim.
    intro t. apply stable_kernel_bisim_refl.
    intros sim Hsim h. destruct h as [r|X e k].
    + constructor. reflexivity.
    + constructor. intro x. exact (Hsim (observe (k x))).
  - exact primitive_ptree_bisim_sym.
  - exact primitive_ptree_bisim_trans.
Qed.

End PrimitivePTreeBisimulationTransitivity.

(** A domain on observed PTree states suitable for relating structured proof
    rules to primitive behavior.  Totality is required for every structured
    frontier of a member, while primitive closure records that residual
    states and visible continuations remain in the domain almost everywhere.
    The latter packages the closure obligations needed by completeness rather
    than scattering them across client theorems. *)
Polymorphic Record BehavioralDomain
    {E : Type -> Type} {MN MF : Type -> Type}
    `{NI : SemanticMeasureInterface MN}
    `{FI : SemanticMeasureInterface MF}
    `{MX : MixedMeasureInterface MN MF}
    `{FO : @SemanticOmegaInterface MF FI}
    {R : Type} (D : ptree' E MN R -> Prop) : Prop := {
  behavioral_frontier_exists : forall ot, D ot ->
    exists out : MF (frontier_head E MN R), frontier ot out;
  behavioral_frontier_total : forall ot, D ot ->
    forall out : MF (frontier_head E MN R),
    frontier ot out -> @sem_total MF FI FO _ out;
  behavioral_primitive_closed : forall ot, D ot ->
    sem_ae (@ptree_primitive_kernel E MN MF FI MX R ot)
      (fun target =>
        match target with
        | SHInternal ot' => D ot'
        | SHStable (FHRet _) => True
        | SHStable (@FHVis _ _ _ X _ k) =>
            forall x : X, D (observe (k x))
        end)
}.

Polymorphic Definition frontier_head_in_domain
    {E : Type -> Type} {MN : Type -> Type} {R : Type}
    (D : ptree' E MN R -> Prop) (head : frontier_head E MN R) : Prop :=
  match head with
  | FHRet _ => True
  | @FHVis _ _ _ X _ k => forall x : X, D (observe (k x))
  end.

Lemma frontier_head_rel_with_domains
    {E : Type -> Type} {MN : Type -> Type} {R1 R2 : Type}
    (RR : R1 -> R2 -> Prop)
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop)
    (D1 : ptree' E MN R1 -> Prop) (D2 : ptree' E MN R2 -> Prop)
    h1 h2 :
  frontier_head_rel RR sim h1 h2 ->
  frontier_head_in_domain D1 h1 ->
  frontier_head_in_domain D2 h2 ->
  frontier_head_rel RR
    (fun t1 t2 => sim t1 t2 /\ D1 (observe t1) /\ D2 (observe t2)) h1 h2.
Proof.
  intros Hrel HD1 HD2. destruct Hrel.
  - constructor. exact H.
  - constructor. intro x. split; [exact (H x)|].
    split; [exact (HD1 x)|exact (HD2 x)].
Qed.

Section BehavioralDomainStableHittingClosure.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FAE : @SemanticMeasureAEKleisliLaws MF FI}
  `{FOAE : @SemanticOmegaAELaws MF FI FO}.
Context {R : Type}.
Variable D : ptree' E MN R -> Prop.
Hypothesis BD : BehavioralDomain (MF := MF) D.

(** [behavioral_primitive_closed] is not merely bookkeeping: via the generic
    unbounded invariant theorem it closes every stable-hitting limit, not
    just a single primitive step. *)
Theorem behavioral_domain_stable_hitting_weak_ae state out :
  D state ->
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R) state out ->
  sem_ae out (frontier_head_in_domain D).
Proof.
  intros HD Hhit.
  eapply stable_hitting_weak_ae with (D := D).
  - intros state' HD'. exact (behavioral_primitive_closed BD HD').
  - exact HD.
  - exact Hhit.
Qed.

Corollary behavioral_domain_stable_hitting_ast_ae state out :
  D state ->
  stable_hitting_ast
    (@ptree_primitive_kernel E MN MF FI MX R) state out ->
  sem_ae out (frontier_head_in_domain D).
Proof.
  intros HD [Hweak _].
  exact (behavioral_domain_stable_hitting_weak_ae HD Hweak).
Qed.

End BehavioralDomainStableHittingClosure.

Section OperationalHittingOrder.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}.

Lemma operational_target_approx_increasing {R} fuel
    (target : operational_target E MN R) :
  sem_le
    (operational_target_approx (MF := MF) fuel target)
    (operational_target_approx (Datatypes.S fuel) target).
Proof.
  induction fuel as [|fuel IH] in target |- *; destruct target as [h|t].
  - apply sem_le_refl.
  - apply sem_zero_le.
  - apply sem_le_refl.
  - apply sem_bind_le_k. exact IH.
Qed.

Theorem operational_hitting_increasing {R} (ot : ptree' E MN R) :
  sem_increasing
    (fun fuel => operational_hitting_approx (MF := MF) fuel ot).
Proof.
  intros fuel. unfold operational_hitting_approx.
  apply sem_bind_le_k. intros target.
  exact (operational_target_approx_increasing fuel target).
Qed.

Theorem operational_hitting_mono {R} (ot : ptree' E MN R) n m :
  Peano.le n m ->
  sem_le (operational_hitting_approx (MF := MF) n ot)
    (operational_hitting_approx (MF := MF) m ot).
Proof.
  intro Hnm. induction Hnm.
  - apply sem_le_refl.
  - eapply sem_le_trans; [exact IHHnm|].
    apply operational_hitting_increasing.
Qed.

End OperationalHittingOrder.

Section OperationalWeakExistence.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}.

Theorem operational_weak_exists {R} (ot : ptree' E MN R) :
  exists out, operational_weak (MF := MF) ot out.
Proof.
  unfold operational_weak. apply sem_lub_exists.
  exact (operational_hitting_increasing ot).
Qed.

Theorem operational_weak_unique {R} (ot : ptree' E MN R) out1 out2 :
  operational_weak (MF := MF) ot out1 ->
  operational_weak (MF := MF) ot out2 ->
  sem_eq out1 out2.
Proof.
  unfold operational_weak. intros H1 H2.
  eapply sem_lub_unique; eassumption.
Qed.

End OperationalWeakExistence.

Section OperationalStableSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}.

Theorem operational_weak_ret {R} (r : R) :
  operational_weak (MF := MF) (RetF r)
    (sem_ret (FHRet r : frontier_head E MN R)).
Proof.
  unfold operational_weak. eapply sem_lub_chain_proper.
  - intro n. apply sem_eq_sym. apply operational_hitting_ret.
  - apply sem_lub_constant.
Qed.

Theorem operational_weak_vis {R X} (e : E X)
    (k : X -> ptree E MN R) :
  operational_weak (MF := MF) (VisF e k)
    (sem_ret (FHVis e k : frontier_head E MN R)).
Proof.
  unfold operational_weak. eapply sem_lub_chain_proper.
  - intro n. apply sem_eq_sym. apply operational_hitting_vis.
  - apply sem_lub_constant.
Qed.

End OperationalStableSoundness.

Section OperationalTauSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}.

Lemma operational_hitting_tau_zero_prefix {R}
    (t : ptree E MN R) fuel :
  sem_eq
    (operational_hitting_approx (MF := MF) fuel (TauF t))
    (sem_zero_prefix
      (fun n => operational_hitting_approx (MF := MF) n (observe t))
      fuel).
Proof.
  destruct fuel as [|fuel].
  - apply operational_hitting_tau_zero.
  - apply operational_hitting_tau_succ.
Qed.

(** A silent primitive step changes only the finite indexing of the hitting
    chain.  Cofinality, rather than a Tau-specific weak constructor, is what
    makes its unbounded behavior invariant. *)
Theorem operational_weak_tau_iff {R} (t : ptree E MN R) out :
  operational_weak (MF := MF) (TauF t) out <->
  operational_weak (MF := MF) (observe t) out.
Proof.
  unfold operational_weak. split; intro Hlim.
  - apply (proj2 (sem_lub_zero_prefix
      (fun n => operational_hitting_approx (MF := MF) n (observe t)) out)).
    eapply sem_lub_chain_proper; [|exact Hlim].
    intro n. apply operational_hitting_tau_zero_prefix.
  - eapply sem_lub_chain_proper.
    + intro n. apply sem_eq_sym.
      apply operational_hitting_tau_zero_prefix.
    + apply (proj1 (sem_lub_zero_prefix
        (fun n => operational_hitting_approx (MF := MF) n (observe t)) out)).
      exact Hlim.
Qed.

Corollary operational_ast_weak_tau_iff {R} (t : ptree E MN R) out :
  operational_ast_weak (MF := MF) (TauF t) out <->
  operational_ast_weak (MF := MF) (observe t) out.
Proof.
  unfold operational_ast_weak. rewrite operational_weak_tau_iff.
  reflexivity.
Qed.

End OperationalTauSoundness.

Section OperationalProbSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.

Lemma operational_hitting_prob_zero_prefix {R X}
    (mu : MN X) (k : X -> ptree E MN R) fuel :
  sem_eq
    (operational_hitting_approx (MF := MF) fuel (ProbF mu k))
    (sem_zero_prefix
      (fun n => mixed_bind mu (fun x =>
        operational_hitting_approx (MF := MF) n (observe (k x))))
      fuel).
Proof.
  destruct fuel as [|fuel].
  - cbn [sem_zero_prefix]. eapply sem_eq_trans.
    + apply operational_hitting_prob_zero.
    + apply mixed_bind_zero.
  - cbn [sem_zero_prefix]. apply operational_hitting_prob_succ.
Qed.

(** Primitive probabilistic sampling commutes with unbounded stable hitting
    exactly under the mixed monotone-convergence capability. *)
Theorem operational_weak_prob {R X}
    (mu : MN X) (k : X -> ptree E MN R)
    (front : X -> MF (frontier_head E MN R)) (Good : X -> Prop) :
  sem_ae mu Good ->
  (forall x, Good x -> operational_weak (MF := MF) (observe (k x)) (front x)) ->
  operational_weak (MF := MF) (ProbF mu k) (mixed_bind mu front).
Proof.
  intros Hae Hbranch. unfold operational_weak in Hbranch |- *.
  eapply sem_lub_chain_proper.
  - intro n. apply sem_eq_sym.
    apply operational_hitting_prob_zero_prefix.
  - apply (proj1 (sem_lub_zero_prefix
      (fun n => mixed_bind mu (fun x =>
        operational_hitting_approx (MF := MF) n (observe (k x))))
      (mixed_bind mu front))).
    eapply mixed_bind_lub; [exact Hae| |exact Hbranch].
    intros x _. apply operational_hitting_increasing.
Qed.

Corollary operational_ast_weak_prob {R X}
    (mu : MN X) (k : X -> ptree E MN R)
    (front : X -> MF (frontier_head E MN R)) (Good : X -> Prop) :
  sem_ae mu Good ->
  (forall x, Good x ->
    operational_ast_weak (MF := MF) (observe (k x)) (front x)) ->
  sem_total (mixed_bind mu front) ->
  operational_ast_weak (MF := MF) (ProbF mu k) (mixed_bind mu front).
Proof.
  intros Hae Hbranch Htotal. split; [|exact Htotal].
  eapply operational_weak_prob; [exact Hae|].
  intros x Hx. exact (proj1 (Hbranch x Hx)).
Qed.

End OperationalProbSoundness.

Section OperationalBindDiagonal.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

Definition operational_head_bind_approx {A R} (fuel : nat)
    (k : A -> ptree E MN R) (h : frontier_head E MN A) :
    MF (frontier_head E MN R) :=
  match h with
  | FHRet a => operational_hitting_approx (MF := MF) fuel (observe (k a))
  | @FHVis _ _ _ X e c =>
      sem_ret (FHVis e (fun x => PTree.bind (c x) k))
  end.

Definition operational_bind_diagonal_approx {A R} (fuel : nat)
    (t : ptree E MN A) (k : A -> ptree E MN R) :
    MF (frontier_head E MN R) :=
  sem_bind (operational_hitting_approx (MF := MF) fuel (observe t))
    (operational_head_bind_approx fuel k).

(** The remaining PTree-specific obligation for Bind: global primitive fuel
    and the diagonal allocation of the same index to source and continuation
    must be cofinal.  This statement contains no frontier derivation and is
    kept separate from measure-level diagonal continuity. *)
Definition operational_bind_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) : Prop :=
  forall out,
    sem_lub (fun fuel => operational_hitting_approx (MF := MF) fuel
      (observe (PTree.bind t k))) out <->
    sem_lub (fun fuel => operational_bind_diagonal_approx fuel t k) out.

End OperationalBindDiagonal.

Section OperationalBindSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}
  `{FDL : @SemanticMeasureDiagonalLaws MF FI FO}.

Lemma operational_head_bind_approx_increasing {A R}
    (k : A -> ptree E MN R) h :
  sem_increasing (fun fuel => operational_head_bind_approx
    (MF := MF) fuel k h).
Proof.
  destruct h as [a|X e c]; intro fuel; cbn [operational_head_bind_approx].
  - apply operational_hitting_increasing.
  - apply sem_le_refl.
Qed.

Lemma operational_head_bind_approx_mono {A R}
    (k : A -> ptree E MN R) h n m :
  Peano.le n m ->
  sem_le (operational_head_bind_approx (MF := MF) n k h)
    (operational_head_bind_approx (MF := MF) m k h).
Proof.
  intro Hnm. destruct h as [a|X e c]; cbn [operational_head_bind_approx].
  - apply operational_hitting_mono. exact Hnm.
  - apply sem_le_refl.
Qed.

Lemma operational_bind_diagonal_mono {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) n m :
  Peano.le n m ->
  sem_le (operational_bind_diagonal_approx (MF := MF) n t k)
    (operational_bind_diagonal_approx (MF := MF) m t k).
Proof.
  intro Hnm. unfold operational_bind_diagonal_approx.
  eapply sem_le_trans.
  - apply sem_bind_le_mu. apply operational_hitting_mono. exact Hnm.
  - apply sem_bind_le_k. intro h.
    apply operational_head_bind_approx_mono. exact Hnm.
Qed.

Lemma operational_head_bind_approx_lub {A R}
    (k : A -> ptree E MN R)
    (front : A -> MF (frontier_head E MN R))
    (Hfront : forall a,
      operational_weak (MF := MF) (observe (k a)) (front a)) h :
  sem_lub (fun fuel => operational_head_bind_approx
      (MF := MF) fuel k h)
    (frontier_head_bind_front k front h).
Proof.
  destruct h as [a|X e c]; cbn [operational_head_bind_approx
    frontier_head_bind_front].
  - exact (Hfront a).
  - apply sem_lub_constant.
Qed.

Theorem operational_weak_bind {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R)
    hs (front : A -> MF (frontier_head E MN R)) :
  operational_bind_cofinal (MF := MF) t k ->
  operational_weak (MF := MF) (observe t) hs ->
  (forall a, operational_weak (MF := MF) (observe (k a)) (front a)) ->
  operational_weak (MF := MF) (observe (PTree.bind t k))
    (sem_bind hs (frontier_head_bind_front k front)).
Proof.
  intros Hcofinal Hsource Hfront. unfold operational_weak in *.
  apply (proj2 (Hcofinal _)).
  unfold operational_bind_diagonal_approx.
  eapply sem_bind_diagonal_lub.
  - apply operational_hitting_increasing.
  - intro h. apply operational_head_bind_approx_increasing.
  - exact Hsource.
  - intro h. apply operational_head_bind_approx_lub. exact Hfront.
Qed.

Corollary operational_ast_weak_bind {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R)
    hs (front : A -> MF (frontier_head E MN R)) :
  operational_bind_cofinal (MF := MF) t k ->
  operational_ast_weak (MF := MF) (observe t) hs ->
  (forall a, operational_ast_weak (MF := MF)
    (observe (k a)) (front a)) ->
  sem_total (sem_bind hs (frontier_head_bind_front k front)) ->
  operational_ast_weak (MF := MF) (observe (PTree.bind t k))
    (sem_bind hs (frontier_head_bind_front k front)).
Proof.
  intros Hcofinal Hsource Hfront Htotal. split; [|exact Htotal].
  eapply operational_weak_bind; [exact Hcofinal|exact (proj1 Hsource)|].
  intro a. exact (proj1 (Hfront a)).
Qed.

End OperationalBindSoundness.

Section OperationalIterationCofinality.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

Definition operational_iter_round_approx {I R} (fuel : nat)
    (transition : I -> MN (I + R)) (i : I) :
    MF (frontier_head E MN R) :=
  sem_bind (mixed_iter_approx fuel transition i)
    (fun r => sem_ret (FHRet r)).

Definition operational_iter_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) : Prop :=
  forall out,
    sem_lub (fun fuel => operational_hitting_approx (MF := MF) fuel
      (observe (PTree.iter step i))) out <->
    sem_lub (fun fuel => operational_iter_round_approx
      fuel transition i) out.

End OperationalIterationCofinality.

Section OperationalIterationSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}.

Theorem operational_weak_iter {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) out :
  sem_increasing (fun fuel => mixed_iter_approx fuel transition i) ->
  operational_iter_cofinal (MF := MF) step transition i ->
  mixed_iter transition i out ->
  operational_weak (MF := MF) (observe (PTree.iter step i))
    (sem_bind out (fun r => sem_ret
      (FHRet r : frontier_head E MN R))).
Proof.
  intros Hinc Hcofinal Hiter. unfold operational_weak.
  apply (proj2 (Hcofinal _)). unfold operational_iter_round_approx.
  eapply sem_bind_lub; [exact Hinc|exact Hiter].
Qed.

Corollary operational_ast_weak_iter {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) out :
  sem_increasing (fun fuel => mixed_iter_approx fuel transition i) ->
  operational_iter_cofinal (MF := MF) step transition i ->
  mixed_iter transition i out ->
  sem_total (sem_bind out (fun r => sem_ret
    (FHRet r : frontier_head E MN R))) ->
  operational_ast_weak (MF := MF) (observe (PTree.iter step i))
    (sem_bind out (fun r => sem_ret
      (FHRet r : frontier_head E MN R))).
Proof.
  intros Hinc Hcofinal Hiter Htotal. split; [|exact Htotal].
  eapply operational_weak_iter; eassumption.
Qed.

End OperationalIterationSoundness.

Section FrontierOperationalSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}
  `{FDL : @SemanticMeasureDiagonalLaws MF FI FO}.

Variable bind_cofinality : forall A R
    (t : ptree E MN A) (k : A -> ptree E MN R),
    operational_bind_cofinal (MF := MF) t k.

Variable iter_productivity : forall I R
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I),
    (forall j, operational_weak (MF := MF) (observe (step j))
      (mixed_bind (transition j)
        (fun next => sem_ret (FHRet next)))) ->
    sem_increasing (fun fuel => mixed_iter_approx fuel transition i) /\
    operational_iter_cofinal (MF := MF) step transition i.

(** Conditional end-to-end soundness of the structured frontier.  The
    analytic assumptions are measure capabilities; the only PTree-specific
    assumptions left are global-vs-diagonal fuel cofinality for Bind and
    productive iteration rounds. *)
Theorem frontier_to_operational_weak {R}
    (ot : ptree' E MN R) out :
  frontier ot out -> operational_weak (MF := MF) ot out.
Proof.
  intro Hfront. induction Hfront.
  - apply operational_weak_ret.
  - apply operational_weak_vis.
  - apply (proj2 (operational_weak_tau_iff t hs)). exact IHHfront.
  - eapply operational_weak_prob; [exact H|exact H1].
  - destruct (iter_productivity (I := I) (R := R)
      (step := step) (transition := transition) i H0)
      as [Hinc Hcofinal].
    eapply operational_weak_iter; eassumption.
  - eapply operational_weak_bind.
    + apply bind_cofinality.
    + exact IHHfront.
    + exact H0.
  - destruct (iter_productivity (I := I) (R := R)
      (step := step) (transition := transition) i H0)
      as [Hinc Hcofinal].
    eapply operational_weak_iter; eassumption.
Qed.

(** Soundness into the syntax-independent standard model.  The conclusion
    mentions only the primitive PTree kernel adapter and generic stable
    hitting; the structured frontier is used solely as a proof system on the
    premise side. *)
Theorem frontier_to_primitive_stable_weak {R}
    (ot : ptree' E MN R) out :
  frontier ot out ->
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R) ot out.
Proof.
  intro Hfront.
  apply (proj2 (ptree_primitive_weak_adequate ot out)).
  exact (frontier_to_operational_weak Hfront).
Qed.

Corollary frontier_to_primitive_stable_ast {R}
    (ot : ptree' E MN R) out :
  frontier ot out -> sem_total out ->
  stable_hitting_ast
    (@ptree_primitive_kernel E MN MF FI MX R) ot out.
Proof.
  intros Hfront Htotal. split.
  - exact (frontier_to_primitive_stable_weak Hfront).
  - exact Htotal.
Qed.

End FrontierOperationalSoundness.

Section StructuredProofNativeSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}
  `{FDL : @SemanticMeasureDiagonalLaws MF FI FO}
  `{UC : @UnifiedFrontierCoherence E MN MF NI FI MX FO}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.
Variable bind_cofinality : forall A R
    (t : ptree E MN A) (k : A -> ptree E MN R),
    operational_bind_cofinal (MF := MF) t k.
Variable iter_productivity : forall I R
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I),
    (forall j, operational_weak (MF := MF) (observe (step j))
      (mixed_bind (transition j)
        (fun next => sem_ret (FHRet next)))) ->
    sem_increasing (fun fuel => mixed_iter_approx fuel transition i) /\
    operational_iter_cofinal (MF := MF) step transition i.
Variable D1 : ptree' E MN R1 -> Prop.
Variable D2 : ptree' E MN R2 -> Prop.
Hypothesis BD1 : BehavioralDomain (MF := MF) D1.
Hypothesis BD2 : BehavioralDomain (MF := MF) D2.

(** Intermediate relation-global closure assumption.  It is deliberately
    separate from [BehavioralDomain]: the latter currently gives only AE
    closure of one primitive kernel, while the coinductive coupling below
    needs pointwise domain membership for every recursive pair.  A genuine
    root-membership theorem must derive this fact via AE preservation through
    stable hitting and coupling restriction. *)
Hypothesis weak_bisim_domain_closed : forall t1 t2,
  @weak_bisim E MN MF NI FI NC FC MX FO R1 R2 RR t1 t2 ->
  D1 (observe t1) /\ D2 (observe t2).

Theorem weak_bisim_to_primitive_ptree_bisim_on_domain : forall t1 t2,
  @weak_bisim E MN MF NI FI NC FC MX FO R1 R2 RR t1 t2 ->
  @primitive_ptree_bisim E MN MF FI FC MX FO R1 R2 RR t1 t2.
Proof.
  unfold primitive_ptree_bisim, primitive_ptree_state_bisim.
  unfold stable_kernel_bisim at 1. coinduction CH CIH.
  intros t1 t2 Hweak.
  pose proof (weak_bisim_unfold Hweak) as Hstep.
  destruct (weak_bisim_domain_closed Hweak) as [HD1 HD2].
  destruct (behavioral_frontier_exists BD1 HD1) as [out1 Hfront1].
  destruct (weak_bisimF_frontier_l Hstep Hfront1)
    as [out2 [Hfront2 Hlift]].
  pose proof (behavioral_frontier_total BD1 HD1 Hfront1) as Htotal1.
  pose proof (behavioral_frontier_total BD2 HD2 Hfront2) as Htotal2.
  pose proof (frontier_to_primitive_stable_ast
    bind_cofinality iter_productivity Hfront1 Htotal1) as Hast1.
  pose proof (frontier_to_primitive_stable_ast
    bind_cofinality iter_productivity Hfront2 Htotal2) as Hast2.
  assert (Hnative : sem_lift
      (ptree_stable_observation_rel RR (elem CH)) out1 out2).
  { eapply sem_lift_mono; [|exact Hlift].
    apply frontier_head_rel_mono. intros u1 u2 Hu.
    exact (CIH _ _ Hu). }
  unfold stable_kernel_bisim_body. eapply SKBAST.
  - split.
    + intros out1' Hast1'. exists out2. split; [exact Hast2|].
      eapply sem_lift_proper_l; [|exact Hnative].
      eapply sem_lub_unique; [exact (proj1 Hast1)|exact (proj1 Hast1')].
    + intros out2' Hast2'. exists out1. split; [exact Hast1|].
      eapply sem_lift_proper_r; [|exact Hnative].
      eapply sem_lub_unique; [exact (proj1 Hast2)|exact (proj1 Hast2')].
  - exact Hast1.
  - exact Hast2.
  - exact Hnative.
Qed.

Hypothesis primitive_bisim_domain_closed : forall t1 t2,
  @primitive_ptree_bisim E MN MF FI FC MX FO R1 R2 RR t1 t2 ->
  D1 (observe t1) /\ D2 (observe t2).

(** Completeness under relation-global domain closure.  Because every domain
    member has a total structured frontier, native AST coherence can be
    realized on both sides and its recursive head coupling becomes the
    coinduction hypothesis for the structured proof relation.  This theorem
    is not yet root-membership closed-domain completeness. *)
Theorem primitive_ptree_bisim_to_weak_bisim_on_domain : forall t1 t2,
  @primitive_ptree_bisim E MN MF FI FC MX FO R1 R2 RR t1 t2 ->
  @weak_bisim E MN MF NI FI NC FC MX FO R1 R2 RR t1 t2.
Proof.
  unfold weak_bisim at 1. coinduction CH CIH.
  intros t1 t2 Hnative.
  destruct (primitive_bisim_domain_closed Hnative) as [HD1 HD2].
  destruct (behavioral_frontier_exists BD1 HD1) as [out1 Hfront1].
  destruct (behavioral_frontier_exists BD2 HD2) as [front2 Hfront2].
  pose proof (behavioral_frontier_total BD1 HD1 Hfront1) as Htotal1.
  pose proof (behavioral_frontier_total BD2 HD2 Hfront2) as Htotal2.
  pose proof (frontier_to_primitive_stable_ast
    bind_cofinality iter_productivity Hfront1 Htotal1) as Hast1.
  pose proof (frontier_to_primitive_stable_ast
    bind_cofinality iter_productivity Hfront2 Htotal2) as Hfront_ast2.
  pose proof Hnative as Hstate.
  unfold primitive_ptree_bisim, primitive_ptree_state_bisim in Hstate.
  destruct (proj1 (stable_kernel_bisim_ast_match Hstate) out1 Hast1)
    as [out2 [Hast2 Hlift]].
  assert (Hout2 : sem_eq out2 front2).
  { eapply sem_lub_unique;
      [exact (proj1 Hast2)|exact (proj1 Hfront_ast2)]. }
  assert (Hlift_front : sem_lift
      (frontier_head_rel RR (elem CH)) out1 front2).
  { eapply sem_lift_mono.
    - apply frontier_head_rel_mono. intros u1 u2 Hu.
      exact (CIH _ _ Hu).
    - eapply sem_lift_proper_r; [exact Hout2|exact Hlift]. }
  unfold weak_bisim_body. eapply UWBFrontier;
    [exact Hfront1|exact Hfront2|exact Hlift_front].
Qed.

Corollary weak_bisim_iff_primitive_ptree_bisim_on_domain t1 t2 :
  @weak_bisim E MN MF NI FI NC FC MX FO R1 R2 RR t1 t2 <->
  @primitive_ptree_bisim E MN MF FI FC MX FO R1 R2 RR t1 t2.
Proof.
  split.
  - apply weak_bisim_to_primitive_ptree_bisim_on_domain.
  - apply primitive_ptree_bisim_to_weak_bisim_on_domain.
Qed.

End StructuredProofNativeSoundness.

Section StructuredProofNativeRootDomainCorrespondence.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{FCA : @SemanticMeasureCouplingAELaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}
  `{FDL : @SemanticMeasureDiagonalLaws MF FI FO}
  `{FAE : @SemanticMeasureAEKleisliLaws MF FI}
  `{FOAE : @SemanticOmegaAELaws MF FI FO}
  `{UC : @UnifiedFrontierCoherence E MN MF NI FI MX FO}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.
Variable bind_cofinality : forall A R
    (t : ptree E MN A) (k : A -> ptree E MN R),
    operational_bind_cofinal (MF := MF) t k.
Variable iter_productivity : forall I R
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I),
    (forall j, operational_weak (MF := MF) (observe (step j))
      (mixed_bind (transition j) (fun next => sem_ret (FHRet next)))) ->
    sem_increasing (fun fuel => mixed_iter_approx fuel transition i) /\
    operational_iter_cofinal (MF := MF) step transition i.
Variable D1 : ptree' E MN R1 -> Prop.
Variable D2 : ptree' E MN R2 -> Prop.
Hypothesis BD1 : BehavioralDomain (MF := MF) D1.
Hypothesis BD2 : BehavioralDomain (MF := MF) D2.

(** Root membership now suffices: stable-hitting AE closure and coupling
    restriction manufacture domain membership for every recursive pair. *)
Theorem weak_bisim_to_primitive_ptree_bisim_root_domain : forall t1 t2,
  @weak_bisim E MN MF NI FI NC FC MX FO R1 R2 RR t1 t2 /\
  D1 (observe t1) /\ D2 (observe t2) ->
  @primitive_ptree_bisim E MN MF FI FC MX FO R1 R2 RR t1 t2.
Proof.
  unfold primitive_ptree_bisim, primitive_ptree_state_bisim.
  unfold stable_kernel_bisim at 1. coinduction CH CIH.
  intros t1 t2 [Hweak [HD1 HD2]].
  pose proof (weak_bisim_unfold Hweak) as Hstep.
  destruct (behavioral_frontier_exists BD1 HD1) as [out1 Hfront1].
  destruct (weak_bisimF_frontier_l Hstep Hfront1)
    as [out2 [Hfront2 Hlift]].
  pose proof (behavioral_frontier_total BD1 HD1 Hfront1) as Htotal1.
  pose proof (behavioral_frontier_total BD2 HD2 Hfront2) as Htotal2.
  pose proof (frontier_to_primitive_stable_ast
    bind_cofinality iter_productivity Hfront1 Htotal1) as Hast1.
  pose proof (frontier_to_primitive_stable_ast
    bind_cofinality iter_productivity Hfront2 Htotal2) as Hast2.
  pose proof (behavioral_domain_stable_hitting_ast_ae BD1 HD1 Hast1)
    as Hae1.
  pose proof (behavioral_domain_stable_hitting_ast_ae BD2 HD2 Hast2)
    as Hae2.
  pose proof (sem_lift_ae_restrict Hlift Hae1 Hae2) as Hrestricted.
  assert (Hnative : sem_lift
      (ptree_stable_observation_rel RR (elem CH)) out1 out2).
  { eapply sem_lift_mono; [|exact Hrestricted].
    intros h1 h2 [Hrel [Hgood1 Hgood2]].
    destruct Hrel.
    - constructor. exact H.
    - constructor. intro x.
      exact (CIH _ _ (conj (H x) (conj (Hgood1 x) (Hgood2 x)))). }
  unfold stable_kernel_bisim_body. eapply SKBAST.
  - split.
    + intros out1' Hast1'. exists out2. split; [exact Hast2|].
      eapply sem_lift_proper_l; [|exact Hnative].
      eapply sem_lub_unique; [exact (proj1 Hast1)|exact (proj1 Hast1')].
    + intros out2' Hast2'. exists out1. split; [exact Hast1|].
      eapply sem_lift_proper_r; [|exact Hnative].
      eapply sem_lub_unique; [exact (proj1 Hast2)|exact (proj1 Hast2')].
  - exact Hast1.
  - exact Hast2.
  - exact Hnative.
Qed.

Theorem primitive_ptree_bisim_to_weak_bisim_root_domain : forall t1 t2,
  @primitive_ptree_bisim E MN MF FI FC MX FO R1 R2 RR t1 t2 /\
  D1 (observe t1) /\ D2 (observe t2) ->
  @weak_bisim E MN MF NI FI NC FC MX FO R1 R2 RR t1 t2.
Proof.
  unfold weak_bisim at 1. coinduction CH CIH.
  intros t1 t2 [Hnative [HD1 HD2]].
  destruct (behavioral_frontier_exists BD1 HD1) as [out1 Hfront1].
  destruct (behavioral_frontier_exists BD2 HD2) as [front2 Hfront2].
  pose proof (behavioral_frontier_total BD1 HD1 Hfront1) as Htotal1.
  pose proof (behavioral_frontier_total BD2 HD2 Hfront2) as Htotal2.
  pose proof (frontier_to_primitive_stable_ast
    bind_cofinality iter_productivity Hfront1 Htotal1) as Hast1.
  pose proof (frontier_to_primitive_stable_ast
    bind_cofinality iter_productivity Hfront2 Htotal2) as Hast2.
  pose proof Hnative as Hstate.
  unfold primitive_ptree_bisim, primitive_ptree_state_bisim in Hstate.
  destruct (proj1 (stable_kernel_bisim_ast_match Hstate) out1 Hast1)
    as [out2 [Hout2ast Hlift]].
  assert (Hout2 : sem_eq out2 front2).
  { eapply sem_lub_unique;
      [exact (proj1 Hout2ast)|exact (proj1 Hast2)]. }
  pose proof (behavioral_domain_stable_hitting_ast_ae BD1 HD1 Hast1)
    as Hae1.
  pose proof (behavioral_domain_stable_hitting_ast_ae BD2 HD2 Hout2ast)
    as Hae2.
  pose proof (sem_lift_ae_restrict Hlift Hae1 Hae2) as Hrestricted.
  assert (Hlift_front : sem_lift
      (frontier_head_rel RR (elem CH)) out1 front2).
  { eapply sem_lift_proper_r; [exact Hout2|].
    eapply sem_lift_mono; [|exact Hrestricted].
    intros h1 h2 [Hrel [Hgood1 Hgood2]].
    destruct Hrel.
    - constructor. exact H.
    - constructor. intro x.
      exact (CIH _ _ (conj (H x) (conj (Hgood1 x) (Hgood2 x)))). }
  unfold weak_bisim_body. eapply UWBFrontier;
    [exact Hfront1|exact Hfront2|exact Hlift_front].
Qed.

Corollary weak_bisim_iff_primitive_ptree_bisim_root_domain t1 t2 :
  D1 (observe t1) -> D2 (observe t2) ->
  (@weak_bisim E MN MF NI FI NC FC MX FO R1 R2 RR t1 t2 <->
   @primitive_ptree_bisim E MN MF FI FC MX FO R1 R2 RR t1 t2).
Proof.
  intros HD1 HD2. split; intro Hrel.
  - apply weak_bisim_to_primitive_ptree_bisim_root_domain.
    exact (conj Hrel (conj HD1 HD2)).
  - apply primitive_ptree_bisim_to_weak_bisim_root_domain.
    exact (conj Hrel (conj HD1 HD2)).
Qed.

End StructuredProofNativeRootDomainCorrespondence.

Section PrimitiveFrontierCompletenessBoundary.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}.

(** The exact non-circular obligation for reverse completeness on a chosen
    domain [Productive].  It asks the structured proof system to realize one
    limit of the independently defined primitive hitting chain.  It does not
    quantify over a preselected frontier result and does not assume the
    desired completeness conclusion for every representation of that limit.

    Typical sufficient proofs split this obligation into: a structural
    decomposition of the program, continuity/cofinality for Bind and nested
    limits, and productivity/totality for unbounded Iter nodes.  It cannot
    hold for unrestricted syntax when the frontier intentionally admits only
    productive iteration while primitive hitting also assigns the zero
    subdistribution to divergence. *)
Definition primitive_frontier_realizable_on
    (Productive : forall R : Type, ptree' E MN R -> Prop) : Prop :=
  forall (R : Type) (ot : ptree' E MN R), Productive R ot ->
    exists out,
      frontier ot out /\
      stable_hitting_weak
        (@ptree_primitive_kernel E MN MF FI MX R) ot out.

Theorem primitive_stable_weak_complete_on
    (Productive : forall R : Type, ptree' E MN R -> Prop)
    (Hrealize : primitive_frontier_realizable_on Productive)
    {R} (ot : ptree' E MN R) out :
  Productive R ot ->
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R) ot out ->
  exists frontier_out,
    frontier ot frontier_out /\ sem_eq out frontier_out.
Proof.
  intros Hproductive Hweak.
  destruct (Hrealize R ot Hproductive) as [frontier_out [Hfront Hfrontweak]].
  exists frontier_out. split; [exact Hfront|].
  eapply stable_hitting_weak_unique; eassumption.
Qed.

End PrimitiveFrontierCompletenessBoundary.

(** Compatibility layer retained for migrated clients.  The public native
    behavioral equivalence is [primitive_ptree_bisim]; this older generator
    mentions PTree Ret/Vis/Tau/Prob shapes directly and is not used by the
    proof/native full-abstraction theorem above. *)
Section GuardedOperationalBisimulationCompatibility.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Definition operational_ast_match
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop)
    (ot1 : ptree' E MN R1) (ot2 : ptree' E MN R2) : Prop :=
  (forall out1, operational_ast_weak (MF := MF) ot1 out1 ->
    exists out2, operational_ast_weak (MF := MF) ot2 out2 /\
      sem_lift (frontier_head_rel RR sim) out1 out2) /\
  (forall out2, operational_ast_weak (MF := MF) ot2 out2 ->
    exists out1, operational_ast_weak (MF := MF) ot1 out1 /\
      sem_lift (frontier_head_rel RR sim) out1 out2).

Inductive operational_bisimF
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop) :
    ptree' E MN R1 -> ptree' E MN R2 -> Prop :=
  | OPBStable ot1 ot2 out1 out2 :
      operational_ast_weak (MF := MF) ot1 out1 ->
      operational_ast_weak (MF := MF) ot2 out2 ->
      sem_lift (frontier_head_rel RR sim) out1 out2 ->
      operational_bisimF sim ot1 ot2
  | OPBRet r1 r2 :
      RR r1 r2 -> operational_bisimF sim (RetF r1) (RetF r2)
  | OPBVis {X : Type} (e : E X) k1 k2 :
      (forall x, sim (k1 x) (k2 x)) ->
      operational_bisimF sim (VisF e k1) (VisF e k2)
  | OPBTau t1 t2 :
      operational_ast_match sim (TauF t1) (TauF t2) ->
      sim t1 t2 -> operational_bisimF sim (TauF t1) (TauF t2)
  | OPBProb {X Y : Type} (mu : MN X) (nu : MN Y) k1 k2 :
      operational_ast_match sim (ProbF mu k1) (ProbF nu k2) ->
      sem_lift (fun x y => sim (k1 x) (k2 y)) mu nu ->
      operational_bisimF sim (ProbF mu k1) (ProbF nu k2)
  | OPBTauL t1 ot2 :
      operational_bisimF sim (observe t1) ot2 ->
      operational_bisimF sim (TauF t1) ot2
  | OPBTauR ot1 t2 :
      operational_bisimF sim ot1 (observe t2) ->
      operational_bisimF sim ot1 (TauF t2).

Lemma operational_ast_match_mono sim1 sim2 ot1 ot2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  operational_ast_match sim1 ot1 ot2 ->
  operational_ast_match sim2 ot1 ot2.
Proof.
  intros Hsim [HL HR]. split; intros out Hweak.
  - destruct (HL _ Hweak) as [out' [Hweak' Hlift]].
    exists out'. split; [exact Hweak'|].
    eapply sem_lift_mono; [|exact Hlift].
    exact (frontier_head_rel_mono Hsim).
  - destruct (HR _ Hweak) as [out' [Hweak' Hlift]].
    exists out'. split; [exact Hweak'|].
    eapply sem_lift_mono; [|exact Hlift].
    exact (frontier_head_rel_mono Hsim).
Qed.

Lemma operational_bisimF_monotone sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall ot1 ot2, operational_bisimF sim1 ot1 ot2 ->
    operational_bisimF sim2 ot1 ot2.
Proof.
  intros Hsim ot1 ot2 Hstep. induction Hstep.
  - eapply OPBStable; [exact H|exact H0|].
    eapply sem_lift_mono; [|exact H1].
    exact (frontier_head_rel_mono Hsim).
  - apply OPBRet. exact H.
  - apply OPBVis. intros x. exact (Hsim _ _ (H x)).
  - apply OPBTau.
    + exact (operational_ast_match_mono Hsim H).
    + exact (Hsim _ _ H0).
  - apply OPBProb.
    + exact (operational_ast_match_mono Hsim H).
    + eapply sem_lift_mono; [|exact H0].
      intros x y Hxy. exact (Hsim _ _ Hxy).
  - exact (OPBTauL IHHstep).
  - exact (OPBTauR IHHstep).
Qed.

Definition operational_bisim_body sim
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) :=
  operational_bisimF sim (observe t1) (observe t2).

Program Definition foperational_bisim :
    mon (ptree E MN R1 -> ptree E MN R2 -> Prop) :=
  {| body := operational_bisim_body |}.
Next Obligation.
  intros sim1 sim2 Hsub t1 t2 Hstep.
  eapply operational_bisimF_monotone; eauto.
Qed.

Definition operational_bisim :
    ptree E MN R1 -> ptree E MN R2 -> Prop :=
  gfp foperational_bisim.

Lemma operational_bisim_unfold t1 t2 :
  operational_bisim t1 t2 ->
  operational_bisimF operational_bisim (observe t1) (observe t2).
Proof.
  intro H. apply (gfp_pfp foperational_bisim) in H. exact H.
Qed.

Lemma operational_bisim_fold t1 t2 :
  operational_bisimF operational_bisim (observe t1) (observe t2) ->
  operational_bisim t1 t2.
Proof.
  intro H. unfold operational_bisim.
  apply (gfp_fp foperational_bisim). exact H.
Qed.

End GuardedOperationalBisimulationCompatibility.

Section GuardedOperationalReflexivity.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

Lemma operational_ast_match_refl {R}
    (sim : ptree E MN R -> ptree E MN R -> Prop)
    (Hhead : Reflexive (frontier_head_rel eq sim)) :
  forall ot, operational_ast_match eq sim ot ot.
Proof.
  intro ot. split; intros out Hweak; exists out; split; auto.
  all: apply sem_lift_refl; exact Hhead.
Qed.

Lemma operational_bisim_refl {R} :
  Reflexive (@operational_bisim E MN MF NI FI NC FC MX FO R R eq).
Proof.
  intro t. revert t. unfold operational_bisim.
  coinduction CH CIH. intro t.
  unfold operational_bisim_body. set (ot := observe t).
  change (operational_bisimF eq (elem CH) ot ot).
  destruct ot as [r|u|X e k|X mu k].
  - apply OPBRet. reflexivity.
  - apply OPBTau.
    + apply operational_ast_match_refl.
      apply unified_head_rel_refl. exact CIH.
    + exact (CIH u).
  - apply OPBVis. intro x. exact (CIH (k x)).
  - apply OPBProb.
    + apply operational_ast_match_refl.
      apply unified_head_rel_refl. exact CIH.
    + apply sem_lift_refl. intro x. exact (CIH (k x)).
Qed.

(** Extensional endpoint principle.  The two AST proofs may use unrelated
    finite hitting chains, productivity arguments, and concrete
    representations of their limits.  Only the resulting stable
    distributions are coupled.  This is the intended entry point for
    comparing an unbounded implementation with a terminating specification;
    it does not require them to share an iteration design. *)
Lemma operational_bisim_of_ast_lift {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) out1 out2 :
  operational_ast_weak (MF := MF) (observe t1) out1 ->
  operational_ast_weak (MF := MF) (observe t2) out2 ->
  sem_lift
    (frontier_head_rel RR
      (@operational_bisim E MN MF NI FI NC FC MX FO R1 R2 RR))
    out1 out2 ->
  @operational_bisim E MN MF NI FI NC FC MX FO R1 R2 RR t1 t2.
Proof.
  intros H1 H2 Hlift. apply operational_bisim_fold.
  exact (OPBStable H1 H2 Hlift).
Qed.

Lemma operational_bisim_of_common_ast {R}
    (t1 t2 : ptree E MN R) out :
  operational_ast_weak (MF := MF) (observe t1) out ->
  operational_ast_weak (MF := MF) (observe t2) out ->
  @operational_bisim E MN MF NI FI NC FC MX FO R R eq t1 t2.
Proof.
  intros H1 H2. eapply operational_bisim_of_ast_lift;
    [exact H1|exact H2|].
  apply sem_lift_refl. apply unified_head_rel_refl.
  exact operational_bisim_refl.
Qed.

End GuardedOperationalReflexivity.
