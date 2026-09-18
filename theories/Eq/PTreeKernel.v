Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Program.
From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PTreeKernel.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.

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

(** Resolve one stable target using at most [fuel] further primitive
    steps.  Unresolved internal mass goes to [sem_zero]. *)
Definition ptree_stable_target_approx {R} (fuel : nat)
    (target : stable_target (ptree' E MN R) (frontier_head E MN R)) :
    MF (frontier_head E MN R) :=
  stable_target_approx ptree_primitive_kernel fuel target.

(** The [fuel]-bounded stable-hitting distribution of an observed state.
    Fuel counts primitive internal transitions.  Ret and Vis are stable after
    their one primitive observation step; Tau and Prob recursively spend the
    remaining fuel through the same kernel. *)
Definition ptree_hitting_approx {R} (fuel : nat)
    (ot : ptree' E MN R) : MF (frontier_head E MN R) :=
  stable_hitting_approx ptree_primitive_kernel fuel ot.

(** The behavior of a tree is the stable-hitting limit of primitive
    execution.  Unresolved weight is absent from each finite approximant.
    On a subprobability backend, pure divergence therefore has the zero
    subdistribution as its hitting limit. *)
Definition ptree_stable_hitting {R} (ot : ptree' E MN R)
    (out : MF (frontier_head E MN R)) : Prop :=
  stable_hitting ptree_primitive_kernel ot out.

(** AST is a separate property of a behavior: its stable-hitting limit
    satisfies the backend's totality predicate.  On a subprobability backend
    this means stable mass one. *)
Definition ptree_stable_hitting_ast {R} (ot : ptree' E MN R)
    (out : MF (frontier_head E MN R)) : Prop :=
  ptree_stable_hitting ot out /\ sem_total out.

(** A syntax-independent bridge for genuinely nested unbounded execution.
    [grid outer inner] may allocate separate fuel to an outer protocol and
    an inner AST sampler.  The program-specific obligation is only that its
    primitive global-fuel chain has the same limits as the diagonal grid.
    Fubini continuity then turns iterated row limits into that diagonal
    limit; no [Bind], [Iter], or [NestedIter] semantic constructor is used. *)
Definition ptree_hitting_diagonal_cofinal {R}
    (ot : ptree' E MN R)
    (grid : nat -> nat -> MF (frontier_head E MN R)) : Prop :=
  forall out,
    sem_lub (fun fuel => ptree_hitting_approx fuel ot) out <->
    sem_lub (fun fuel => grid fuel fuel) out.

Section KernelNestedGrid.
Context `{FFubini : @SemanticOmegaFubiniLaws MF FI FO}.

Theorem ptree_stable_hitting_of_nested_grid {R}
    (ot : ptree' E MN R)
    (grid : nat -> nat -> MF (frontier_head E MN R))
    (row_out : nat -> MF (frontier_head E MN R)) out :
  ptree_hitting_diagonal_cofinal ot grid ->
  (forall outer, sem_increasing (grid outer)) ->
  (forall inner, sem_increasing (fun outer => grid outer inner)) ->
  (forall outer, sem_lub (grid outer) (row_out outer)) ->
  sem_lub row_out out ->
  ptree_stable_hitting ot out.
Proof.
  intros Hcofinal Hinner Houter Hrows Hout.
  unfold ptree_stable_hitting.
  apply (proj2 (Hcofinal out)).
  eapply sem_lub_double_diagonal; eassumption.
Qed.

Corollary ptree_stable_hitting_ast_of_nested_grid {R}
    (ot : ptree' E MN R)
    (grid : nat -> nat -> MF (frontier_head E MN R))
    (row_out : nat -> MF (frontier_head E MN R)) out :
  ptree_hitting_diagonal_cofinal ot grid ->
  (forall outer, sem_increasing (grid outer)) ->
  (forall inner, sem_increasing (fun outer => grid outer inner)) ->
  (forall outer, sem_lub (grid outer) (row_out outer)) ->
  sem_lub row_out out ->
  sem_total out ->
  ptree_stable_hitting_ast ot out.
Proof.
  intros Hcofinal Hinner Houter Hrows Hout Htotal.
  split; [|exact Htotal].
  eapply ptree_stable_hitting_of_nested_grid; eassumption.
Qed.

End KernelNestedGrid.

Lemma ptree_kernel_retE {R} (r : R) :
  ptree_primitive_kernel (RetF r) =
  sem_ret (SHStable (FHRet r)).
Proof. reflexivity. Qed.

Lemma ptree_kernel_visE {R X} (e : E X)
    (k : X -> ptree E MN R) :
  ptree_primitive_kernel (VisF e k) =
  sem_ret (SHStable (FHVis e k)).
Proof. reflexivity. Qed.

Lemma ptree_kernel_tauE {R} (t : ptree E MN R) :
  ptree_primitive_kernel (TauF t) = sem_ret (SHInternal (observe t)).
Proof. reflexivity. Qed.

Lemma ptree_kernel_probE {R X} (mu : MN X)
    (k : X -> ptree E MN R) :
  ptree_primitive_kernel (ProbF mu k) =
  mixed_bind mu (fun x => sem_ret (SHInternal (observe (k x)))).
Proof. reflexivity. Qed.

Lemma ptree_target_stableE {R} fuel
    (h : frontier_head E MN R) :
  ptree_stable_target_approx fuel (SHStable h) = sem_ret h.
Proof. destruct fuel; reflexivity. Qed.

Lemma ptree_target_internal_zeroE {R} (t : ptree' E MN R) :
  ptree_stable_target_approx O (SHInternal t) = sem_zero.
Proof. reflexivity. Qed.

Lemma ptree_target_internal_succE {R} fuel
    (t : ptree' E MN R) :
  ptree_stable_target_approx (Datatypes.S fuel)
    (SHInternal t) =
  sem_bind (ptree_primitive_kernel t)
    (ptree_stable_target_approx fuel).
Proof. reflexivity. Qed.

End PTreeKernel.

Section PTreeKernelLaws.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI}.

(** These equations are derived from the single primitive kernel.  They
    are not constructors of stable-hitting semantics. *)
Lemma ptree_hitting_ret {R} fuel (r : R) :
  sem_eq (ptree_hitting_approx (MF := MF) fuel (RetF r))
    (sem_ret (FHRet r : frontier_head E MN R)).
Proof.
  unfold ptree_hitting_approx, stable_hitting_approx,
    ptree_primitive_kernel.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite stable_target_stableE. apply sem_eq_refl.
Qed.

Lemma ptree_hitting_vis {R X} fuel (e : E X)
    (k : X -> ptree E MN R) :
  sem_eq (ptree_hitting_approx (MF := MF) fuel (VisF e k))
    (sem_ret (FHVis e k : frontier_head E MN R)).
Proof.
  unfold ptree_hitting_approx, stable_hitting_approx,
    ptree_primitive_kernel.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite stable_target_stableE. apply sem_eq_refl.
Qed.

Lemma ptree_hitting_tau_zero {R} (t : ptree E MN R) :
  sem_eq (ptree_hitting_approx (MF := MF) O (TauF t)) sem_zero.
Proof.
  unfold ptree_hitting_approx, stable_hitting_approx,
    ptree_primitive_kernel.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite stable_target_internal_zeroE. apply sem_eq_refl.
Qed.

Lemma ptree_hitting_tau_succ {R} fuel (t : ptree E MN R) :
  sem_eq
    (ptree_hitting_approx (MF := MF) (Datatypes.S fuel) (TauF t))
    (ptree_hitting_approx fuel (observe t)).
Proof.
  unfold ptree_hitting_approx, stable_hitting_approx at 1.
  unfold ptree_primitive_kernel.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite stable_target_internal_succE. apply sem_eq_refl.
Qed.

Lemma ptree_hitting_prob {R X} fuel (mu : MN X)
    (k : X -> ptree E MN R) :
  sem_eq (ptree_hitting_approx (MF := MF) fuel (ProbF mu k))
    (mixed_bind mu (fun x =>
      ptree_stable_target_approx fuel (SHInternal (observe (k x))))).
Proof.
  unfold ptree_hitting_approx, stable_hitting_approx,
    ptree_primitive_kernel.
  eapply sem_eq_trans.
  - apply mixed_bind_assoc.
  - apply mixed_bind_ae_proper.
    eapply sem_ae_mono; [|apply sem_ae_true].
    intros x _. apply sem_bind_ret_l.
Qed.

Lemma ptree_hitting_prob_zero {R X} (mu : MN X)
    (k : X -> ptree E MN R) :
  sem_eq (ptree_hitting_approx (MF := MF) O (ProbF mu k))
    (mixed_bind mu (fun _ => sem_zero)).
Proof.
  eapply sem_eq_trans; [apply ptree_hitting_prob|].
  apply mixed_bind_ae_proper.
  eapply sem_ae_mono; [|apply sem_ae_true].
  intros x _. rewrite ptree_target_internal_zeroE. apply sem_eq_refl.
Qed.

Lemma ptree_hitting_prob_succ {R X} fuel (mu : MN X)
    (k : X -> ptree E MN R) :
  sem_eq
    (ptree_hitting_approx (MF := MF) (Datatypes.S fuel) (ProbF mu k))
    (mixed_bind mu (fun x =>
      ptree_hitting_approx fuel (observe (k x)))).
Proof.
  eapply sem_eq_trans; [apply ptree_hitting_prob|].
  apply mixed_bind_ae_proper.
  eapply sem_ae_mono; [|apply sem_ae_true].
  intros x _. rewrite ptree_target_internal_succE. apply sem_eq_refl.
Qed.

End PTreeKernelLaws.

Section GenericKernelAdequacy.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI}.

(** Adequacy of the PTree adapter for the syntax-independent primitive
    kernel semantics.  This is pointwise in finite fuel, so the later
    and AST correspondence does not assume omega-limit uniqueness or a
    structured frontier derivation. *)
Theorem ptree_primitive_hitting_adequate {R} fuel
    (ot : ptree' E MN R) :
  sem_eq
    (stable_hitting_approx
      (@ptree_primitive_kernel E MN MF FI MX R) fuel ot)
    (ptree_hitting_approx (MF := MF) fuel ot).
Proof.
  induction fuel as [|fuel IH] in ot |- *; destruct ot as [r|t|X e k|X mu k].
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_stableE.
    apply sem_eq_sym. apply ptree_hitting_ret.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_internal_zeroE.
    apply sem_eq_sym. apply ptree_hitting_tau_zero.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_stableE.
    apply sem_eq_sym. apply ptree_hitting_vis.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply mixed_bind_assoc|].
    eapply sem_eq_trans.
    + apply mixed_bind_ae_proper.
      eapply sem_ae_mono; [|apply sem_ae_true].
      intros x _. eapply sem_eq_trans; [apply sem_bind_ret_l|].
      rewrite stable_target_internal_zeroE. apply sem_eq_refl.
    + apply sem_eq_sym. apply ptree_hitting_prob_zero.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_stableE.
    apply sem_eq_sym. apply ptree_hitting_ret.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_internal_succE.
    eapply sem_eq_trans; [apply IH|].
    apply sem_eq_sym. apply ptree_hitting_tau_succ.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_stableE.
    apply sem_eq_sym. apply ptree_hitting_vis.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply mixed_bind_assoc|].
    eapply sem_eq_trans.
    + apply mixed_bind_ae_proper.
      eapply sem_ae_mono; [|apply sem_ae_true].
      intros x _. eapply sem_eq_trans; [apply sem_bind_ret_l|].
      rewrite stable_target_internal_succE. apply IH.
    + apply sem_eq_sym. apply ptree_hitting_prob_succ.
Qed.

Context `{FOL : @SemanticOmegaLaws MF FI FO}.

Theorem ptree_primitive_stable_hitting_adequate {R}
    (ot : ptree' E MN R) out :
  stable_hitting
      (@ptree_primitive_kernel E MN MF FI MX R) ot out <->
  ptree_stable_hitting (MF := MF) ot out.
Proof.
  unfold stable_hitting, ptree_stable_hitting. split; intro Hlim.
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
  ptree_stable_hitting_ast (MF := MF) ot out.
Proof.
  unfold stable_hitting_ast, ptree_stable_hitting_ast.
  rewrite ptree_primitive_stable_hitting_adequate. reflexivity.
Qed.

End GenericKernelAdequacy.


Section KernelHittingOrder.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}.

Lemma ptree_target_approx_increasing {R} fuel
    (target : stable_target (ptree' E MN R) (frontier_head E MN R)) :
  sem_le
    (ptree_stable_target_approx (MF := MF) fuel target)
    (ptree_stable_target_approx (Datatypes.S fuel) target).
Proof.
  induction fuel as [|fuel IH] in target |- *; destruct target as [h|t].
  - apply sem_le_refl.
  - apply sem_zero_le.
  - apply sem_le_refl.
  - apply sem_bind_le_k. exact IH.
Qed.

Theorem ptree_hitting_increasing {R} (ot : ptree' E MN R) :
  sem_increasing
    (fun fuel => ptree_hitting_approx (MF := MF) fuel ot).
Proof.
  intros fuel. unfold ptree_hitting_approx.
  apply sem_bind_le_k. intros target.
  exact (ptree_target_approx_increasing fuel target).
Qed.

Theorem ptree_hitting_mono {R} (ot : ptree' E MN R) n m :
  Peano.le n m ->
  sem_le (ptree_hitting_approx (MF := MF) n ot)
    (ptree_hitting_approx (MF := MF) m ot).
Proof.
  intro Hnm. induction Hnm.
  - apply sem_le_refl.
  - eapply sem_le_trans; [exact IHHnm|].
    apply ptree_hitting_increasing.
Qed.

End KernelHittingOrder.

Section KernelHittingExistence.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}.

Theorem ptree_stable_hitting_exists {R} (ot : ptree' E MN R) :
  exists out, ptree_stable_hitting (MF := MF) ot out.
Proof.
  unfold ptree_stable_hitting. apply sem_lub_exists.
  exact (ptree_hitting_increasing ot).
Qed.

Theorem ptree_stable_hitting_unique {R} (ot : ptree' E MN R) out1 out2 :
  ptree_stable_hitting (MF := MF) ot out1 ->
  ptree_stable_hitting (MF := MF) ot out2 ->
  sem_eq out1 out2.
Proof.
  unfold ptree_stable_hitting. intros H1 H2.
  eapply sem_lub_unique; eassumption.
Qed.

End KernelHittingExistence.

Section KernelStableSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}.

Theorem ptree_stable_hitting_ret {R} (r : R) :
  ptree_stable_hitting (MF := MF) (RetF r)
    (sem_ret (FHRet r : frontier_head E MN R)).
Proof.
  unfold ptree_stable_hitting. eapply sem_lub_chain_proper.
  - intro n. apply sem_eq_sym. apply ptree_hitting_ret.
  - apply sem_lub_constant.
Qed.

Theorem ptree_stable_hitting_vis {R X} (e : E X)
    (k : X -> ptree E MN R) :
  ptree_stable_hitting (MF := MF) (VisF e k)
    (sem_ret (FHVis e k : frontier_head E MN R)).
Proof.
  unfold ptree_stable_hitting. eapply sem_lub_chain_proper.
  - intro n. apply sem_eq_sym. apply ptree_hitting_vis.
  - apply sem_lub_constant.
Qed.

End KernelStableSoundness.

Section KernelTauSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}.

Lemma ptree_hitting_tau_zero_prefix {R}
    (t : ptree E MN R) fuel :
  sem_eq
    (ptree_hitting_approx (MF := MF) fuel (TauF t))
    (sem_zero_prefix
      (fun n => ptree_hitting_approx (MF := MF) n (observe t))
      fuel).
Proof.
  destruct fuel as [|fuel].
  - apply ptree_hitting_tau_zero.
  - apply ptree_hitting_tau_succ.
Qed.

(** A silent primitive step changes only the finite indexing of the hitting
    chain.  Cofinality, rather than a Tau-specific constructor, is what
    makes its unbounded behavior invariant. *)
Theorem ptree_stable_hitting_tau_iff {R} (t : ptree E MN R) out :
  ptree_stable_hitting (MF := MF) (TauF t) out <->
  ptree_stable_hitting (MF := MF) (observe t) out.
Proof.
  unfold ptree_stable_hitting. split; intro Hlim.
  - apply (proj2 (sem_lub_zero_prefix
      (fun n => ptree_hitting_approx (MF := MF) n (observe t)) out)).
    eapply sem_lub_chain_proper; [|exact Hlim].
    intro n. apply ptree_hitting_tau_zero_prefix.
  - eapply sem_lub_chain_proper.
    + intro n. apply sem_eq_sym.
      apply ptree_hitting_tau_zero_prefix.
    + apply (proj1 (sem_lub_zero_prefix
        (fun n => ptree_hitting_approx (MF := MF) n (observe t)) out)).
      exact Hlim.
Qed.

Corollary ptree_stable_hitting_ast_tau_iff {R} (t : ptree E MN R) out :
  ptree_stable_hitting_ast (MF := MF) (TauF t) out <->
  ptree_stable_hitting_ast (MF := MF) (observe t) out.
Proof.
  unfold ptree_stable_hitting_ast. rewrite ptree_stable_hitting_tau_iff.
  reflexivity.
Qed.

End KernelTauSoundness.

Section KernelProbSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.

Lemma ptree_hitting_prob_zero_prefix {R X}
    (mu : MN X) (k : X -> ptree E MN R) fuel :
  sem_eq
    (ptree_hitting_approx (MF := MF) fuel (ProbF mu k))
    (sem_zero_prefix
      (fun n => mixed_bind mu (fun x =>
        ptree_hitting_approx (MF := MF) n (observe (k x))))
      fuel).
Proof.
  destruct fuel as [|fuel].
  - cbn [sem_zero_prefix]. eapply sem_eq_trans.
    + apply ptree_hitting_prob_zero.
    + apply mixed_bind_zero.
  - cbn [sem_zero_prefix]. apply ptree_hitting_prob_succ.
Qed.

(** Primitive probabilistic sampling commutes with unbounded stable hitting
    exactly under the mixed monotone-convergence capability. *)
Theorem ptree_stable_hitting_prob {R X}
    (mu : MN X) (k : X -> ptree E MN R)
    (front : X -> MF (frontier_head E MN R)) (Good : X -> Prop) :
  sem_ae mu Good ->
  (forall x, Good x -> ptree_stable_hitting (MF := MF) (observe (k x)) (front x)) ->
  ptree_stable_hitting (MF := MF) (ProbF mu k) (mixed_bind mu front).
Proof.
  intros Hae Hbranch. unfold ptree_stable_hitting in Hbranch |- *.
  eapply sem_lub_chain_proper.
  - intro n. apply sem_eq_sym.
    apply ptree_hitting_prob_zero_prefix.
  - apply (proj1 (sem_lub_zero_prefix
      (fun n => mixed_bind mu (fun x =>
        ptree_hitting_approx (MF := MF) n (observe (k x))))
      (mixed_bind mu front))).
    eapply mixed_bind_lub; [exact Hae| |exact Hbranch].
    intros x _. apply ptree_hitting_increasing.
Qed.

Corollary ptree_stable_hitting_ast_prob {R X}
    (mu : MN X) (k : X -> ptree E MN R)
    (front : X -> MF (frontier_head E MN R)) (Good : X -> Prop) :
  sem_ae mu Good ->
  (forall x, Good x ->
    ptree_stable_hitting_ast (MF := MF) (observe (k x)) (front x)) ->
  sem_total (mixed_bind mu front) ->
  ptree_stable_hitting_ast (MF := MF) (ProbF mu k) (mixed_bind mu front).
Proof.
  intros Hae Hbranch Htotal. split; [|exact Htotal].
  eapply ptree_stable_hitting_prob; [exact Hae|].
  intros x Hx. exact (proj1 (Hbranch x Hx)).
Qed.

End KernelProbSoundness.

Section KernelBindDiagonal.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.

Definition ptree_head_bind_approx {A R} (fuel : nat)
    (k : A -> ptree E MN R) (h : frontier_head E MN A) :
    MF (frontier_head E MN R) :=
  match h with
  | FHRet a => ptree_hitting_approx (MF := MF) fuel (observe (k a))
  | @FHVis _ _ _ X e c =>
      sem_ret (FHVis e (fun x => PTree.bind (c x) k))
  end.

Definition ptree_bind_diagonal_approx {A R} (fuel : nat)
    (t : ptree E MN A) (k : A -> ptree E MN R) :
    MF (frontier_head E MN R) :=
  sem_bind (ptree_hitting_approx (MF := MF) fuel (observe t))
    (ptree_head_bind_approx fuel k).

(** The remaining PTree-specific obligation for Bind: global primitive fuel
    and the diagonal allocation of the same index to source and continuation
    must be cofinal.  This statement contains no frontier derivation and is
    kept separate from measure-level diagonal continuity. *)
Definition ptree_bind_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) : Prop :=
  forall out,
    sem_lub (fun fuel => ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.bind t k))) out <->
    sem_lub (fun fuel => ptree_bind_diagonal_approx fuel t k) out.

End KernelBindDiagonal.

Section KernelBindSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}
  `{FDL : @SemanticMeasureDiagonalLaws MF FI FO}.

Lemma ptree_head_bind_approx_increasing {A R}
    (k : A -> ptree E MN R) h :
  sem_increasing (fun fuel => ptree_head_bind_approx
    (MF := MF) fuel k h).
Proof.
  destruct h as [a|X e c]; intro fuel; cbn [ptree_head_bind_approx].
  - apply ptree_hitting_increasing.
  - apply sem_le_refl.
Qed.

Lemma ptree_head_bind_approx_mono {A R}
    (k : A -> ptree E MN R) h n m :
  Peano.le n m ->
  sem_le (ptree_head_bind_approx (MF := MF) n k h)
    (ptree_head_bind_approx (MF := MF) m k h).
Proof.
  intro Hnm. destruct h as [a|X e c]; cbn [ptree_head_bind_approx].
  - apply ptree_hitting_mono. exact Hnm.
  - apply sem_le_refl.
Qed.

Lemma ptree_bind_diagonal_mono {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) n m :
  Peano.le n m ->
  sem_le (ptree_bind_diagonal_approx (MF := MF) n t k)
    (ptree_bind_diagonal_approx (MF := MF) m t k).
Proof.
  intro Hnm. unfold ptree_bind_diagonal_approx.
  eapply sem_le_trans.
  - apply sem_bind_le_mu. apply ptree_hitting_mono. exact Hnm.
  - apply sem_bind_le_k. intro h.
    apply ptree_head_bind_approx_mono. exact Hnm.
Qed.

Lemma ptree_head_bind_approx_lub {A R}
    (k : A -> ptree E MN R)
    (front : A -> MF (frontier_head E MN R))
    (Hfront : forall a,
      ptree_stable_hitting (MF := MF) (observe (k a)) (front a)) h :
  sem_lub (fun fuel => ptree_head_bind_approx
      (MF := MF) fuel k h)
    (frontier_head_bind_front k front h).
Proof.
  destruct h as [a|X e c]; cbn [ptree_head_bind_approx
    frontier_head_bind_front].
  - exact (Hfront a).
  - apply sem_lub_constant.
Qed.

Theorem ptree_stable_hitting_bind {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R)
    hs (front : A -> MF (frontier_head E MN R)) :
  ptree_bind_cofinal (MF := MF) t k ->
  ptree_stable_hitting (MF := MF) (observe t) hs ->
  (forall a, ptree_stable_hitting (MF := MF) (observe (k a)) (front a)) ->
  ptree_stable_hitting (MF := MF) (observe (PTree.bind t k))
    (sem_bind hs (frontier_head_bind_front k front)).
Proof.
  intros Hcofinal Hsource Hfront. unfold ptree_stable_hitting in *.
  apply (proj2 (Hcofinal _)).
  unfold ptree_bind_diagonal_approx.
  eapply sem_bind_diagonal_lub.
  - apply ptree_hitting_increasing.
  - intro h. apply ptree_head_bind_approx_increasing.
  - exact Hsource.
  - intro h. apply ptree_head_bind_approx_lub. exact Hfront.
Qed.

Corollary ptree_stable_hitting_ast_bind {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R)
    hs (front : A -> MF (frontier_head E MN R)) :
  ptree_bind_cofinal (MF := MF) t k ->
  ptree_stable_hitting_ast (MF := MF) (observe t) hs ->
  (forall a, ptree_stable_hitting_ast (MF := MF)
    (observe (k a)) (front a)) ->
  sem_total (sem_bind hs (frontier_head_bind_front k front)) ->
  ptree_stable_hitting_ast (MF := MF) (observe (PTree.bind t k))
    (sem_bind hs (frontier_head_bind_front k front)).
Proof.
  intros Hcofinal Hsource Hfront Htotal. split; [|exact Htotal].
  eapply ptree_stable_hitting_bind; [exact Hcofinal|exact (proj1 Hsource)|].
  intro a. exact (proj1 (Hfront a)).
Qed.

End KernelBindSoundness.

Section KernelInterpDiagonal.
Context {E F : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.

Definition ptree_interp_head_tree {R}
    (handler : forall X, E X -> ptree F MN X)
    (h : frontier_head E MN R) : ptree F MN R :=
  match h with
  | FHRet r => Ret r
  | @FHVis _ _ _ X e k =>
      Tau (PTree.bind (@handler X e)
        (fun x => PTree.interp handler (k x)))
  end.

Definition ptree_interp_head_approx {R}
    (fuel : nat) (handler : forall X, E X -> ptree F MN X)
    (h : frontier_head E MN R) :
    MF (frontier_head F MN R) :=
  ptree_hitting_approx (MF := MF) fuel
    (observe (ptree_interp_head_tree handler h)).

Definition ptree_interp_diagonal_approx {R}
    (fuel : nat) (handler : forall X, E X -> ptree F MN X)
    (t : ptree E MN R) : MF (frontier_head F MN R) :=
  sem_bind
    (ptree_hitting_approx (MF := MF) fuel (observe t))
    (ptree_interp_head_approx fuel handler).

Definition ptree_interp_cofinal {R}
    (handler : forall X, E X -> ptree F MN X)
    (t : ptree E MN R) : Prop :=
  forall out,
    sem_lub (fun fuel => ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.interp handler t))) out <->
    sem_lub (fun fuel => ptree_interp_diagonal_approx
      fuel handler t) out.

End KernelInterpDiagonal.

Section KernelInterpSoundness.
Context {E F : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}
  `{FDL : @SemanticMeasureDiagonalLaws MF FI FO}.

Lemma ptree_interp_head_approx_increasing {R}
    (handler : forall X, E X -> ptree F MN X)
    (h : frontier_head E MN R) :
  sem_increasing (fun fuel => ptree_interp_head_approx
    (MF := MF) fuel handler h).
Proof.
  intro fuel. apply ptree_hitting_increasing.
Qed.

Lemma ptree_interp_head_approx_lub {R}
    (handler : forall X, E X -> ptree F MN X)
    (front : frontier_head E MN R -> MF (frontier_head F MN R))
    (Hfront : forall h, ptree_stable_hitting (MF := MF)
      (observe (ptree_interp_head_tree handler h)) (front h)) h :
  sem_lub (fun fuel => ptree_interp_head_approx
      (MF := MF) fuel handler h) (front h).
Proof.
  exact (Hfront h).
Qed.

Theorem ptree_stable_hitting_interp {R}
    (handler : forall X, E X -> ptree F MN X)
    (t : ptree E MN R)
    hs (front : frontier_head E MN R -> MF (frontier_head F MN R)) :
  ptree_interp_cofinal (MF := MF) handler t ->
  ptree_stable_hitting (MF := MF) (observe t) hs ->
  (forall h, ptree_stable_hitting (MF := MF)
    (observe (ptree_interp_head_tree handler h)) (front h)) ->
  ptree_stable_hitting (MF := MF) (observe (PTree.interp handler t))
    (sem_bind hs front).
Proof.
  intros Hcofinal Hsource Hfront. unfold ptree_stable_hitting in *.
  apply (proj2 (Hcofinal _)).
  unfold ptree_interp_diagonal_approx.
  eapply sem_bind_diagonal_lub.
  - apply ptree_hitting_increasing.
  - intro h. apply ptree_interp_head_approx_increasing.
  - exact Hsource.
  - intro h. apply ptree_interp_head_approx_lub. exact Hfront.
Qed.

End KernelInterpSoundness.

Section KernelIterationCofinality.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.

Definition ptree_iter_round_approx {I R} (fuel : nat)
    (transition : I -> MN (I + R)) (i : I) :
    MF (frontier_head E MN R) :=
  sem_bind (mixed_iter_approx fuel transition i)
    (fun r => sem_ret (FHRet r)).

Definition ptree_iter_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) : Prop :=
  forall out,
    sem_lub (fun fuel => ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.iter step i))) out <->
    sem_lub (fun fuel => ptree_iter_round_approx
      fuel transition i) out.

End KernelIterationCofinality.

Section KernelIterationSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}.

Theorem ptree_stable_hitting_iter {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) out :
  sem_increasing (fun fuel => mixed_iter_approx fuel transition i) ->
  ptree_iter_cofinal (MF := MF) step transition i ->
  mixed_iter transition i out ->
  ptree_stable_hitting (MF := MF) (observe (PTree.iter step i))
    (sem_bind out (fun r => sem_ret
      (FHRet r : frontier_head E MN R))).
Proof.
  intros Hinc Hcofinal Hiter. unfold ptree_stable_hitting.
  apply (proj2 (Hcofinal _)). unfold ptree_iter_round_approx.
  eapply sem_bind_lub; [exact Hinc|exact Hiter].
Qed.

Corollary ptree_stable_hitting_ast_iter {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) out :
  sem_increasing (fun fuel => mixed_iter_approx fuel transition i) ->
  ptree_iter_cofinal (MF := MF) step transition i ->
  mixed_iter transition i out ->
  sem_total (sem_bind out (fun r => sem_ret
    (FHRet r : frontier_head E MN R))) ->
  ptree_stable_hitting_ast (MF := MF) (observe (PTree.iter step i))
    (sem_bind out (fun r => sem_ret
      (FHRet r : frontier_head E MN R))).
Proof.
  intros Hinc Hcofinal Hiter Htotal. split; [|exact Htotal].
  eapply ptree_stable_hitting_iter; eassumption.
Qed.

End KernelIterationSoundness.

Section FrontierKernelSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}
  `{FDL : @SemanticMeasureDiagonalLaws MF FI FO}.

Variable bind_cofinality : forall A R
    (t : ptree E MN A) (k : A -> ptree E MN R),
    ptree_bind_cofinal (MF := MF) t k.

Variable iter_productivity : forall I R
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I),
    (forall j, ptree_stable_hitting (MF := MF) (observe (step j))
      (mixed_bind (transition j)
        (fun next => sem_ret (FHRet next)))) ->
    sem_increasing (fun fuel => mixed_iter_approx fuel transition i) /\
    ptree_iter_cofinal (MF := MF) step transition i.

(** Conditional end-to-end soundness of the structured frontier.  The
    analytic assumptions are measure capabilities; the only PTree-specific
    assumptions left are global-vs-diagonal fuel cofinality for Bind and
    productive iteration rounds. *)
Theorem frontier_to_ptree_stable_hitting {R}
    (ot : ptree' E MN R) out :
  frontier ot out -> ptree_stable_hitting (MF := MF) ot out.
Proof.
  intro Hfront. induction Hfront.
  - apply ptree_stable_hitting_ret.
  - apply ptree_stable_hitting_vis.
  - apply (proj2 (ptree_stable_hitting_tau_iff t hs)). exact IHHfront.
  - eapply ptree_stable_hitting_prob; [exact H|exact H1].
  - destruct (iter_productivity (I := I) (R := R)
      (step := step) (transition := transition) i H0)
      as [Hinc Hcofinal].
    eapply ptree_stable_hitting_iter; eassumption.
  - eapply ptree_stable_hitting_bind.
    + apply bind_cofinality.
    + exact IHHfront.
    + exact H0.
Qed.

(** Soundness into the syntax-independent standard model.  The conclusion
    mentions only the primitive PTree kernel adapter and generic stable
    hitting; the structured frontier is used solely as a proof system on the
    premise side. *)
Theorem frontier_to_stable_hitting {R}
    (ot : ptree' E MN R) out :
  frontier ot out ->
  stable_hitting
    (@ptree_primitive_kernel E MN MF FI MX R) ot out.
Proof.
  intro Hfront.
  apply (proj2 (ptree_primitive_stable_hitting_adequate ot out)).
  exact (frontier_to_ptree_stable_hitting Hfront).
Qed.

Corollary frontier_to_stable_hitting_ast {R}
    (ot : ptree' E MN R) out :
  frontier ot out -> sem_total out ->
  stable_hitting_ast
    (@ptree_primitive_kernel E MN MF FI MX R) ot out.
Proof.
  intros Hfront Htotal. split.
  - exact (frontier_to_stable_hitting Hfront).
  - exact Htotal.
Qed.

End FrontierKernelSoundness.
