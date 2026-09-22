(** Finite-real relational contracts: no rational transport, external domain,
    or FreeOmega is needed to build native couplings. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure AE Coupling.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Backend.SubEnumQ.Measure.SubEnumQ.
Set Implicit Arguments.
Unset Strict Implicit.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Section NativeContracts.
Variable R : realType.
Local Notation M := (SubEnumR R).
Local Notation NI := (SubEnumR_SemanticMeasure R).
Definition real_native_core : @SemanticMeasureCoreLaws M NI := _.
Definition real_native_bind : @SemanticMeasureBindLaws M NI := _.
Definition real_native_ae_lift : @SemanticMeasureAELiftLaws M NI := _.
Definition real_native_coupling_ae : @SemanticMeasureCouplingAELaws M NI := _.

(** Splitting into duplicate entries must not require a normalized or
    duplicate-free representation, nor an inhabited carrier. *)
Definition duplicated_half : M bool.
Proof.
  refine (@subenumR_of_list R bool [(1/4,true); (1/4,true); (0,false)] _ _).
  - intros p b [H|[H|[H|[]]]]; inversion H; subst;
      first [exact: lexx | apply divr_ge0; first [exact: ler01 | exact: ler0n]].
  - cbn; rewrite !mulr1 add0r addr0 -mulr2n -mulr_natl.
    rewrite mulrA mulr1 ler_pdivrMr ?ltr0n // mul1r; exact: ler_nat.
Defined.

Example duplicate_partial_coupling :
  subenumR_lift eq duplicated_half duplicated_half.
Proof. apply subenumR_lift_diagonal; intros p x Hin Hnz; reflexivity. Qed.

(** A genuinely crossed pair of graph couplings. The common measure is
    shared extensionally; composition is not a diagonal-only proof. *)
Example flipped_twice_composition (mu : M bool) :
  subenumR_lift eq mu (subenumR_map negb (subenumR_map negb mu)).
Proof.
  change (@sem_lift M NI bool bool eq mu (subenumR_map negb (subenumR_map negb mu))).
  have Hc := subenumR_lift_comp (subenumR_lift_map negb mu)
    (subenumR_lift_map negb (subenumR_map negb mu)).
  eapply sem_lift_mono; [|exact Hc].
  intros x z [y [Hxy Hyz]]; subst y z; by rewrite negbK.
Qed.

Example relational_bind_heterogeneous {A B C D} (S : A -> B -> Prop) (T : C -> D -> Prop)
  (mu : M A) (nu : M B) (k : A -> M C) (h : B -> M D) :
  sem_lift S mu nu -> (forall x y, S x y -> sem_lift T (k x) (h y)) ->
  sem_lift T (sem_bind mu k) (sem_bind nu h).
Proof. exact: sem_lift_bind. Qed.

Example zero_empty_coupling :
  subenumR_lift (fun (_ : Empty_set) (_ : bool) => False)
    (subenumR_zero R) (subenumR_zero R).
Proof.
  exists (@subenumR_zero R (Empty_set*bool)); split; first by intro f.
  split; first by intro g.
  intros p x [].
Qed.

Example duplicate_zero_branch_ae : subenumR_ae duplicated_half (fun b => b = true).
Proof.
  intros p b [H|[H|[H|[]]]] Hnz; inversion H; subst; try reflexivity.
  exfalso; exact (Hnz (Logic.eq_refl _)).
Qed.
Example duplicate_zero_branch_restrict :
  subenumR_lift (fun x y => x = y /\ x = true /\ y = true) duplicated_half duplicated_half.
Proof.
  change (@sem_lift M NI bool bool (fun x y => x = y /\ x = true /\ y = true)
    duplicated_half duplicated_half).
  apply sem_lift_ae_restrict; try exact duplicate_zero_branch_ae.
  exact duplicate_partial_coupling.
Qed.
End NativeContracts.
