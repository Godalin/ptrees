(** Contract regression for the independent mathematical domain (DS1a).
    No FreeOmega syntax or semantic-interface instances are needed. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Domain Require Import Expectation.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Core.PTreeDefinition.ptree.

Section Tests.
Variable R : realType.

Definition bool_indicator (b : bool) : R := if b then 1 else 0.
Lemma bool_indicator_test : oval_test bool_indicator.
Proof. intros []; split; try exact: lexx; exact: ler01. Qed.

Example distinct_diracs : ~ oval_eq (oval_ret R true) (oval_ret R false).
Proof.
  intro H; have H10 := H bool_indicator bool_indicator_test.
  change (1 = (0 : R)) in H10.
  have Hneq : (1 : R) != 0 by apply oner_neq0.
  by rewrite H10 eqxx in Hneq.
Qed.

Example bottom_is_not_dirac : ~ oval_eq (@oval_bottom R bool) (oval_ret R true).
Proof.
  intro H; have H01 := H (fun _ => 1) (oval_test_one R).
  change (0 = (1 : R)) in H01.
  have Hneq : (1 : R) != 0 by apply oner_neq0.
  by rewrite -H01 eqxx in Hneq.
Qed.

(** A genuinely increasing, nonconstant chain; its supremum is a Dirac. *)
Definition delayed_dirac (n : nat) : OmegaVal R bool :=
  match n with O => oval_bottom R | S _ => oval_ret R true end.
Lemma delayed_increasing : oval_increasing delayed_dirac.
Proof. intros [|n]; [apply oval_bottom_le|apply oval_le_refl]. Qed.
Example delayed_lub : oval_eq (oval_lub delayed_increasing) (oval_ret R true).
Proof.
  apply oval_le_antisym.
  - apply oval_lub_least; intros [|n]; [apply oval_bottom_le|apply oval_le_refl].
  - exact (oval_lub_upper delayed_increasing 1%nat).
Qed.

Definition alternating (n : nat) : OmegaVal R bool :=
  oval_ret R (Nat.even n).
Example alternating_not_increasing : ~ oval_increasing alternating.
Proof.
  intro H; have H10 := H 0%nat bool_indicator bool_indicator_test.
  change (is_true ((1 : R) <= 0)) in H10.
  by rewrite ler10 in H10.
Qed.

(** Supplying the raw sequence is not enough: a monotonicity proof is part
    of the operation, not an assumed global axiom. *)
Fail Definition arbitrary_lub : OmegaVal R bool := oval_lub alternating.

Example both_arguments_grow
    (k : nat -> bool -> OmegaVal R bool)
    (Hk : forall x, oval_increasing (fun n => k n x)) :
  oval_eq (oval_bind (oval_lub delayed_increasing) (fun x => oval_lub (Hk x)))
    (oval_lub (oval_bind_chain_diagonal delayed_increasing Hk)).
Proof. apply oval_bind_double_diagonal. Qed.

Example empty_carrier_has_zero_mass (L : OmegaVal R Empty_set) :
  oval_mass L = 0.
Proof.
  unfold oval_mass.
  rewrite (oval_eval_ext L (f := fun _ => 1) (g := fun _ => 0));
    [exact (oval_zero (oval_laws L))|intros []].
Qed.

(** Antisymmetry identifies bounded-test behavior, not record proof fields. *)
Example mutual_order_is_observational_equality {A} (L M : OmegaVal R A) :
  oval_le L M -> oval_le M L -> oval_eq L M.
Proof. apply oval_le_antisym. Qed.

(** Two lawful evaluators can disagree off the contracted test space. *)
Definition off_test_eval (f : bool -> R) : R := if 1 < f true then 1 else 0.
Lemma off_test_zero f : oval_test f -> off_test_eval f = 0.
Proof.
  move=> Hf; rewrite /off_test_eval ltNge (proj2 (Hf true)); reflexivity.
Qed.
Definition off_test_bottom : OmegaVal R bool.
Proof.
  refine (@Build_OmegaVal R bool off_test_eval _).
  apply (oval_laws_ext (oval_laws (@oval_bottom R bool))).
  intros f Hf; symmetry; exact (off_test_zero f Hf).
Defined.
Example equality_ignores_unbounded_tests : oval_eq off_test_bottom (oval_bottom R).
Proof. intros f Hf; exact (off_test_zero f Hf). Qed.
Example evaluators_still_differ :
  oval_eval off_test_bottom (fun _ => 1 + 1) = 1 /\
  oval_eval (@oval_bottom R bool) (fun _ => 1 + 1) = 0.
Proof. split; last reflexivity. change ((if (1 : R) < 1 + 1 then (1 : R) else 0) = 1).
  by rewrite ltrDl ltr01.
Qed.

End Tests.

(** The result carrier may itself contain types; it is not forced down to
    the scalar field's universe or to an inhabited MathComp carrier. *)
Section HighCarrier.
Universe u.
Variable R : realType.
Definition high_dirac (A : Type@{u}) : OmegaVal R Type@{u} := oval_ret R A.
Example high_right_unit (A : Type@{u}) :
  oval_eq (oval_bind (high_dirac A) (fun X => oval_ret R X)) (high_dirac A).
Proof. apply oval_bind_ret_r. Qed.
End HighCarrier.
