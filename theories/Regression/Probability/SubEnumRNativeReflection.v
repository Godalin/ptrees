(** Explicit validation clients, not a new mainline backend instance.
    Native reflection retains the entire original sampling distribution;
    the generic MDP proof is consumed, never copied. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure SemanticCoupling.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Observation StructuralMeasure Quotient Native NativeCoupling.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
From PTree.Prob.Backend.SubEnumR.FreeOmega Require Import NativeReflection.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import PEutt.
From PTree.Prob.FreeOmega Require Import Measure.
From PTree.Semantics Require Import MDPEmbedding HeadTransition MDPFragment TreeTransitionBisim.
From PTree.Semantics.FreeOmega Require Import MDPReflection MDPCoincidenceFreeOmega.
From PTree.Regression.Backend Require Import SubEnumRRelational.
Set Implicit Arguments.
Unset Strict Implicit.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Contracts.
Variable R : realType.
Local Notation MN := (SubEnumR R).
Local Notation NI := (SubEnumR_SemanticMeasure R).
Local Notation NO := (SubEnumR_SemanticOmega R).
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).

Fail Definition no_automatic_validation_instance :
  @FreeOmegaNativeCouplingLaws MN NI NO := _.

Example mapped_native_reflection {X Y A B} (mu : MN X) (nu : MN Y)
    (f : X -> A) (g : Y -> B) (T : A -> B -> Prop) :
  free_omega_qlift T (FOSample mu (fun x => FORet (f x)))
    (FOSample nu (fun y => FORet (g y))) ->
  sem_lift (fun x y => T (f x) (g y)) mu nu.
Proof.
  exact (@free_omega_sampled_heads_reflect MN NI
    (SubEnumR_SemanticMeasureCoreLaws R) (SubEnumR_SemanticMeasureCouplingAELaws R)
    NO (subenumR_validated_native_coupling R) X Y A B mu nu f g T).
Qed.

(** A noninjective decoder erases both hidden bits, but the returned joint
    must retain the original partial/duplicate native marginals. *)
Example duplicate_partial_decoded_joint :
  exists joint : MN (bool * bool),
    @semantic_coupling MN NI bool bool (fun _ _ => tt = tt)
      (duplicated_half R) (subenumR_map negb (duplicated_half R)) joint.
Proof.
  pose p : free_omega_native_presentation MN unit :=
    {| native_sample_type := bool; native_sample_measure := duplicated_half R;
       native_sample_value := fun _ => tt |}.
  pose q : free_omega_native_presentation MN unit :=
    {| native_sample_type := bool;
       native_sample_measure := subenumR_map negb (duplicated_half R);
       native_sample_value := fun _ => tt |}.
  apply (subenumR_native_quotient_coupling (p := p) (q := q) (T := eq)).
  eapply FOQLSample; [exact (subenumR_lift_map negb (duplicated_half R))|].
  intros x y _; apply FOQLStructural, FOLRet; reflexivity.
Qed.

Example empty_native_joint : exists joint : MN (Empty_set * bool),
  @semantic_coupling MN NI Empty_set bool (fun _ _ => False)
    (subenumR_zero R) (subenumR_zero R) joint.
Proof.
  apply (subenumR_native_quotient_coupling
    (p := {| native_sample_type := Empty_set; native_sample_measure := subenumR_zero R;
             native_sample_value := fun x => x |})
    (q := {| native_sample_type := bool; native_sample_measure := subenumR_zero R;
             native_sample_value := fun y => y |}) (T := fun _ _ => False)).
  eapply FOQLSample; [exact (zero_empty_coupling R)|].
  intros x; destruct x.
Qed.

Variable D : MDP MN.
Local Notation E := (mdpE (mdp_observations D) (mdp_actions D)).

Example validated_mdp_peutt_iff s t :
  mdp_bisim (D := D) s t <->
  @peutt E MN MF FI FC FreeOmegaMixedMeasure FO unit unit eq (mdp_encode s) (mdp_encode t).
Proof. exact (free_mdp_peutt_iff (NJ := subenumR_validated_native_coupling R) (D := D) s t). Qed.

Example validated_mdp_head_bisim_iff s t :
  mdp_bisim (D := D) s t <->
  @head_bisim E MN MF FI FC FreeOmegaMixedMeasure FO unit unit eq
    (mdp_encode_head s) (mdp_encode_head t).
Proof. exact (free_mdp_head_bisim_iff (NJ := subenumR_validated_native_coupling R) (D := D) s t). Qed.

Example validated_encode_mdp_state s :
  @mdp_state E MN MF FI FC FreeOmegaMixedMeasure FO unit (mdp_encode (D := D) s).
Proof.
  apply (mdp_encode_mdp_state (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)).
  - intros t a; apply free_omega_observable_total_intro.
    exists unit, (fun _ => tt),
      (subenumR_bind (mdp_transition D t a) (fun _ => subenumR_ret R tt)).
    split.
    + change (free_omega_observes (NI := NI) (fun _ => tt)
        (FOSample (mdp_transition D t a) (fun u => FORet (mdp_encode_head (D := D) u)))
        (@sem_bind MN NI _ _ (mdp_transition D t a) (fun _ => subenumR_ret R tt))).
      eapply FOOObserveSample; intro u; constructor.
    + change (subenumR_expect
        (subenumR_bind (mdp_transition D t a) (fun _ => subenumR_ret R tt)) (fun _ => 1) = 1).
      rewrite subenumR_expect_bind.
      change (subenumR_expect (mdp_transition D t a) (fun _ => 1 * 1 + 0) = 1).
      rewrite mulr1 addr0; exact (mdp_transition_total D t a).
  - intros t a; eapply FOAESample with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros u _; constructor; exists u; reflexivity.
Qed.

Example validated_mdp_tree_trans_bisim_iff s t :
  mdp_bisim (D := D) s t <->
  @tree_trans_bisim E MN MF FI FC FreeOmegaMixedMeasure FO unit unit eq
    (mdp_encode s) (mdp_encode t).
Proof.
  rewrite validated_mdp_peutt_iff.
  apply (free_mdp_state_peutt_tree_trans_iff (NI := NI) (NO := NO));
    apply validated_encode_mdp_state.
Qed.
End Contracts.

Section LargeDecodedValues.
Universe u v.
Variable R : realType.
Example type_valued_native_joint (A : Type@{u}) (B : Type@{v}) :
  exists joint : SubEnumR R (unit * unit),
    @semantic_coupling (SubEnumR R) (SubEnumR_SemanticMeasure R) unit unit
      (fun _ _ => True) (subenumR_ret R tt) (subenumR_ret R tt) joint.
Proof.
  pose p : free_omega_native_presentation (SubEnumR R) Type@{u} :=
    {| native_sample_type := unit; native_sample_measure := subenumR_ret R tt;
       native_sample_value := fun _ => A |}.
  pose q : free_omega_native_presentation (SubEnumR R) Type@{v} :=
    {| native_sample_type := unit; native_sample_measure := subenumR_ret R tt;
       native_sample_value := fun _ => B |}.
  apply (subenumR_native_quotient_coupling (p := p) (q := q) (T := fun _ _ => True)).
  eapply FOQLSample; [apply sem_lift_refl; intros x; reflexivity|].
  intros x y _; apply FOQLStructural, FOLRet; exact I.
Qed.
End LargeDecodedValues.
