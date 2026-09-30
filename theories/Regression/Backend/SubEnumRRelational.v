(** Finite-real relational contracts: no rational transport, external domain,
    or FreeOmega is needed to build native couplings. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure AE Coupling.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling.
Fail Check PTree.Prob.Backend.SubEnumR.Representation.Build_SubEnumR.
Fail Check PTree.Prob.Backend.SubEnumR.Representation.SubEnumR_rect.
Fail Check PTree.Prob.Legacy.RatSubTypes.nnQ.
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

(** Shared finite containers are the native carrier, not a conversion layer. *)
Example shared_carrier {A} : SubEnumR R A = FiniteSubdist R A.
Proof. reflexivity. Qed.
Example shared_bind {A B} (mu : SubEnumR R A) (k : A -> FiniteSubdist R B) :
  subenumR_bind mu k = finite_subdist_bind mu k.
Proof. reflexivity. Qed.
Example shared_expectation {A} (mu : SubEnumR R A) f :
  subenumR_expect mu f = finite_subdist_expect mu f.
Proof. reflexivity. Qed.
Example shared_raw_projection {A} (mu : SubEnumR R A) :
  subenumR_raw mu = finite_enum_raw (finite_subdist_enum mu).
Proof. reflexivity. Qed.

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

Section HighCarrier.
Universe u.
Variable R : realType.
Definition high_shared_native (A : Type@{u}) : SubEnumR R Type@{u} := finite_subdist_ret R A.
Example high_shared_native_bind (A : Type@{u}) (f : Type@{u} -> R) :
  subenumR_expect (subenumR_bind (high_shared_native A) (fun X => finite_subdist_ret R X)) f = f A.
Proof.
  change (finite_subdist_expect
    (finite_subdist_bind (finite_subdist_ret R A) (fun X => finite_subdist_ret R X)) f = f A).
  by rewrite finite_subdist_bind_ret_r finite_subdist_expect_ret.
Qed.
End HighCarrier.
