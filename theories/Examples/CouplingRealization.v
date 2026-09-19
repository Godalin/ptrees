Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum
  SemanticCoupling SemanticCouplingEnum FreeOmegaMeasure FreeOmegaCoupling
  FreeOmegaCouplingEnum.

Set Implicit Arguments.

(** The node witness API does not impose decidable equality on sampled
    values, including function-valued carriers. *)
Example subenum_function_coupling_realizes
    (R : (nat -> bool) -> (nat -> bool) -> Prop)
    (mu nu : SubEnum (nat -> bool)) :
  @sem_lift SubEnum SubEnum_SemanticMeasure _ _ R mu nu ->
  exists joint, @semantic_coupling SubEnum SubEnum_SemanticMeasure _ _
    R mu nu joint.
Proof. apply subenum_coupling_realization. Qed.

(** Structural witness extraction descends through formal omega nodes. *)
Example subenum_structural_lub_realizes {A B} (R : A -> B -> Prop)
    (left : nat -> FreeOmega SubEnum A) (right : nat -> FreeOmega SubEnum B) :
  (forall n, free_omega_lift R (left n) (right n)) ->
  exists joint, @semantic_coupling (FreeOmega SubEnum)
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    A B R (FOLub left) (FOLub right) joint.
Proof.
  intro H. apply free_subenum_structural_coupling_realization, FOLLub. exact H.
Qed.

(** General relations (not just function graphs) can retain a structural
    joint across quotient rewrites of both marginals. *)
Example subenum_relational_constant_limits_realize {A B}
    (R : A -> B -> Prop) (mu : FreeOmega SubEnum A) (nu : FreeOmega SubEnum B) :
  free_omega_lift R mu nu ->
  exists joint, @semantic_coupling (FreeOmega SubEnum)
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    A B R (FOLub (fun _ => mu)) (FOLub (fun _ => nu)) joint.
Proof.
  intro Hlift. eapply free_omega_lift_realization_mod_eq.
  - exact (@subenum_coupling_realization).
  - exact Hlift.
  - apply FOQLLubConstantR, free_omega_qlift_refl. intro x. reflexivity.
  - apply FOQLLubConstantR, free_omega_qlift_refl. intro y. reflexivity.
Qed.

(** Equality realization is genuinely quotient-level: the two expressions
    below cannot be related by the shape-preserving structural lifting. *)
Definition point : FreeOmega SubEnum bool := FORet true.
Definition point_limit : FreeOmega SubEnum bool := FOLub (fun _ => point).

Example point_limit_not_structural : ~ free_omega_lift eq point point_limit.
Proof. intro H. inversion H. Qed.

Example point_limit_quotient_realizes :
  @semantic_coupling (FreeOmega SubEnum)
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    bool bool eq point point_limit (free_omega_graph_joint (fun x => x) point).
Proof.
  apply free_omega_qlift_eq_realization.
  apply FOQLLubConstantR, free_omega_qlift_refl. intro x. reflexivity.
Qed.

Section RealizationClosure.
Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).

(** A full quotient graph coupling at the source, followed by arbitrary
    relational branch couplings.  The right branches deliberately change
    representation: witness extraction cannot just use structural bind. *)
Example quotient_graph_bind_realizes {A B C D} (f : A -> B)
    (T : C -> D -> Prop) (mu : MF A) (nu : MF B)
    (k : A -> MF C) (h : B -> MF D) :
  free_omega_qlift (fun x y => f x = y) mu nu ->
  (forall x, free_omega_lift T (k x) (h (f x))) ->
  exists joint, @semantic_coupling MF FI C D T
    (free_omega_bind mu k)
    (free_omega_bind nu (fun y => FOLub (fun _ => h y))) joint.
Proof.
  intros Hsource Hbranches.
  eapply (semantic_coupling_bind_realization (M := MF) (MI := FI))
    with (R := fun x y => f x = y).
  - eexists. exact (free_omega_qlift_graph_realization Hsource).
  - intros x y <-. eapply free_omega_lift_realization_mod_eq.
    + exact (@subenum_coupling_realization).
    + exact (Hbranches x).
    + apply free_omega_qlift_refl. intro z. reflexivity.
    + apply FOQLLubConstantR, free_omega_qlift_refl. intro z. reflexivity.
Qed.

(** Node sampling composes realized quotient branches; it does not require
    every branch coupling itself to have a structural lifting derivation. *)
Example sample_quotient_branches_realize {X Y A B}
    (S : X -> Y -> Prop) (R : A -> B -> Prop)
    (mu : SubEnum X) (nu : SubEnum Y) (k : X -> MF A) (h : Y -> MF B) :
  @sem_lift SubEnum SubEnum_SemanticMeasure X Y S mu nu ->
  (forall x y, S x y -> free_omega_lift R (k x) (h y)) ->
  exists joint, @semantic_coupling MF FI A B R
    (FOSample mu k) (FOSample nu (fun y => FOLub (fun _ => h y))) joint.
Proof.
  intros Hnode Hbranches. eapply free_omega_sample_coupling_realization.
  - exact (@subenum_coupling_realization).
  - exact Hnode.
  - intros x y Hxy. eapply free_omega_lift_realization_mod_eq.
    + exact (@subenum_coupling_realization).
    + exact (Hbranches x y Hxy).
    + apply free_omega_qlift_refl. intro z. reflexivity.
    + apply FOQLLubConstantR, free_omega_qlift_refl. intro z. reflexivity.
Qed.

Example point_limit_converse_realizes :
  @semantic_coupling MF FI bool bool (fun y x => x = y)
    point_limit point
    (free_omega_bind (free_omega_graph_joint (fun x => x) point)
      (fun p => FORet (snd p, fst p))).
Proof.
  exact (free_omega_coupling_converse
    (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)
    point_limit_quotient_realizes).
Qed.

(** Both AE restrictions keep the original joint, including its mass. *)
Example point_limit_restricted_same_joint :
  @semantic_coupling MF FI bool bool
    (fun x y => x = y /\ x = true /\ y = true) point point_limit
    (free_omega_graph_joint (fun x => x) point).
Proof.
  apply semantic_coupling_ae_restrict.
  - exact point_limit_quotient_realizes.
  - apply FOAERet. reflexivity.
  - apply FOAELub. intro n. apply FOAERet. reflexivity.
Qed.

(** Existential branch selection needs no inhabitants of the result types,
    and no witness at unrelated source pairs. *)
Example empty_result_bind_realizes :
  exists joint, @semantic_coupling MF FI Empty_set Empty_set
    (fun _ _ => False)
    (free_omega_bind (FOZero : MF bool) (fun _ => FOZero))
    (free_omega_bind (FOZero : MF bool) (fun _ => FOZero)) joint.
Proof.
  eapply (semantic_coupling_bind_realization (M := MF) (MI := FI))
    with (R := fun _ _ : bool => False)
      (mu := FOZero) (nu := FOZero)
      (k := fun _ => FOZero : MF Empty_set)
      (h := fun _ => FOZero : MF Empty_set).
  - exists FOZero. split; [apply FOQLStructural, FOLZero|].
    split; [apply FOQLStructural, FOLZero|apply FOAEZero].
  - intros x y Hfalse. contradiction.
Qed.

(** Formal Lub composition accepts arbitrary realized rows.  This checks
    witness extraction only, not monotonicity of those row witnesses. *)
Example quotient_rows_lub_realize {A B} (R : A -> B -> Prop)
    (left : nat -> MF A) (right : nat -> MF B) :
  (forall n, free_omega_lift R (left n) (right n)) ->
  exists joint, @semantic_coupling MF FI A B R
    (FOLub left) (FOLub (fun n => FOLub (fun _ => right n))) joint.
Proof.
  intro Hrows. apply free_omega_lub_coupling_realization. intro n.
  eapply free_omega_lift_realization_mod_eq.
  - exact (@subenum_coupling_realization).
  - exact (Hrows n).
  - apply free_omega_qlift_refl. intro z. reflexivity.
  - apply FOQLLubConstantR, free_omega_qlift_refl. intro z. reflexivity.
Qed.

End RealizationClosure.

Section FiberGluing.
Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).

Definition embedded_node {A} (mu : SubEnum A) : MF A :=
  FOSample mu (fun x => FORet x).

Lemma embedded_node_coupling {A B} (R : A -> B -> Prop)
    (mu : SubEnum A) (nu : SubEnum B) joint :
  @semantic_coupling SubEnum SubEnum_SemanticMeasure A B R mu nu joint ->
  @semantic_coupling MF FI A B R
    (embedded_node mu) (embedded_node nu) (embedded_node joint).
Proof.
  intros [Hl [Hr Hae]]. split.
  - eapply FOQLSample; [exact Hl|].
    intros p x Hpx. apply FOQLStructural, FOLRet. exact Hpx.
  - split.
    + eapply FOQLSample; [exact Hr|].
      intros p y Hpy. apply FOQLStructural, FOLRet. exact Hpy.
    + eapply FOAESample; [exact Hae|].
      intros p Hp. apply FOAERet. exact Hp.
Qed.

(** Truly relational node couplings (not necessarily function graphs)
    supply the fiber match.  Outer marginals use a different, quotient
    representation.  No fiber-realization or gluing axiom is assumed. *)
Example embedded_node_quotient_gluing {A B C}
    (R : A -> B -> Prop) (T : B -> C -> Prop)
    (mu : SubEnum A) (mid : SubEnum B) (nu : SubEnum C) :
  @sem_lift SubEnum SubEnum_SemanticMeasure A B R mu mid ->
  @sem_lift SubEnum SubEnum_SemanticMeasure B C T mid nu ->
  exists joint, @semantic_coupling MF FI A C
    (fun x z => exists y, R x y /\ T y z)
    (FOLub (fun _ => embedded_node mu))
    (FOLub (fun _ => embedded_node nu)) joint.
Proof.
  intros Hleft Hright.
  destruct (subenum_coupling_realization Hleft) as [jl Hl].
  destruct (subenum_coupling_realization Hright) as [jr Hr].
  assert (Hfiber : free_omega_lift (fun p q => snd p = fst q)
    (embedded_node jl) (embedded_node jr)).
  { eapply FOLSample.
    - exact (semantic_coupling_fiber_lift Hl Hr).
    - intros p q Hpq. apply FOLRet. exact Hpq. }
  destruct (free_omega_coupling_glue_structural
    (@subenum_coupling_realization)
    (embedded_node_coupling Hl) (embedded_node_coupling Hr) Hfiber)
    as [joint Hjoint].
  exists joint. eapply semantic_coupling_transport; [| |exact Hjoint].
  - apply FOQLLubConstantR, free_omega_qlift_refl. intro x. reflexivity.
  - apply FOQLLubConstantR, free_omega_qlift_refl. intro z. reflexivity.
Qed.

(** Independent copies of a nondegenerate bit do NOT match their middle
    values almost everywhere.  Product sampling cannot replace gluing. *)
Example independent_copies_fail_fiber (mu : SubEnum bool)
    (both_values : forall P, @sem_ae SubEnum SubEnum_SemanticMeasure bool mu P ->
      P true /\ P false) :
  ~ free_omega_ae (fun w : (bool * bool) * (bool * bool) =>
      snd (fst w) = fst (snd w))
    (FOSample mu (fun x => FOSample mu (fun y => FORet ((x,x),(y,y))))).
Proof.
  intro Hae. apply free_omega_ae_sample_inv in Hae.
  destruct (both_values _ Hae) as [Htrue _].
  apply free_omega_ae_sample_inv in Htrue.
  destruct (both_values _ Htrue) as [_ Hfalse].
  inversion Hfalse. discriminate.
Qed.

End FiberGluing.
