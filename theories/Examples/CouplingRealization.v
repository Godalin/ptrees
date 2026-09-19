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
