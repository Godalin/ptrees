(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Logic Require Import ClassicalDescription.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype finset bigop ssralg ssrnum order rat reals.
Require Import PTree.Prob.Backend.Common.RatSubTypes PTree.Prob.Backend.Enum.Representation PTree.Prob.Backend.Enum.Iteration.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnum.Measure.
From PTree.Prob.Interface Require Import SemanticCoupling.
Require Import PTree.Prob.Backend.Enum.SemanticCoupling PTree.Prob.Backend.Common.FiniteMatching PTree.Prob.Backend.Common.FiniteRationalTransport PTree.Prob.Backend.Enum.FiniteTransport PTree.Prob.Backend.Enum.FinitePresentation.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Native.
Require Import PTree.Prob.Backend.SubEnum.FreeOmega.Recovery PTree.Prob.Backend.SubEnum.FreeOmega.UpperExpectation PTree.Prob.Backend.SubEnum.FreeOmega.UpperRelational PTree.Prob.Backend.SubEnum.FreeOmega.UpperQuotient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section NativeTransport.
Variable F : realType.
Section FiniteCarrier.
Context {Anchor : Type}.
Local Notation sample := (fun X (mu : SubEnum X) =>
  (FOSample mu FORet : FreeOmegaAt SubEnum Anchor X)).

(** Scalar soundness of the FULL quotient, specialized to native finite
    measures.  No equivalence assumption on the relation is used. *)
Lemma subenum_quotient_rational_tests {A B} (T : A -> B -> Prop)
    (mu : SubEnum A) (nu : SubEnum B) f g :
  free_omega_qlift T (sample A mu) (sample B nu) ->
  (forall x, 0 <= f x /\ f x <= 1) ->
  (forall y, 0 <= g y /\ g y <= 1) ->
  (forall x y, T x y -> f x <= g y) ->
  enum_expect f (subenum_raw mu) <= enum_expect g (subenum_raw nu).
Proof.
  intros Hq Hf Hg Hfg.
  have Hf' : bounded_test (fun x => (ratr (f x) : F)).
  { intro x. split.
    - rewrite ler0q. exact (proj1 (Hf x)).
    - rewrite -(rmorph1 (ratr : {rmorphism rat -> F})) ler_rat. exact (proj2 (Hf x)). }
  have Hg' : bounded_test (fun y => (ratr (g y) : F)).
  { intro y. split.
    - rewrite ler0q. exact (proj1 (Hg y)).
    - rewrite -(rmorph1 (ratr : {rmorphism rat -> F})) ler_rat. exact (proj2 (Hg y)). }
  have Hfg' : forall x y, T x y -> (ratr (f x) : F) <= ratr (g y).
  { intros x y Hxy. rewrite ler_rat. exact (Hfg x y Hxy). }
  have H := free_omega_qlift_upper Hq Hf' Hg' Hfg'.
  change (is_true (enum_real_expect (fun x => (ratr (f x) : F)) (subenum_raw mu) <=
    enum_real_expect (fun y => (ratr (g y) : F)) (subenum_raw nu))) in H.
  by rewrite !enum_real_expect_rat ler_rat in H.
Qed.

Lemma subenum_quotient_equal_mass {A B} (T : A -> B -> Prop)
    (mu : SubEnum A) (nu : SubEnum B) :
  free_omega_qlift T (sample A mu) (sample B nu) ->
  enum_mass (subenum_raw mu) = enum_mass (subenum_raw nu).
Proof.
  intro Hq. have H := free_omega_qlift_upper_mass F Hq.
  change (enum_real_expect (fun _ => (1 : F)) (subenum_raw mu) =
    enum_real_expect (fun _ => (1 : F)) (subenum_raw nu)) in H.
  rewrite !enum_real_expect_one in H.
  exact (fmorph_inj (ratr : {rmorphism rat -> F}) H).
Qed.

(** Hall inequalities follow from indicator tests.  Together with equal
    mass they construct a joint; they are NOT an extra backend axiom. *)
Theorem subenum_finite_quotient_joint {X Y : finType} (edge : X -> Y -> bool)
    (mu : SubEnum X) (nu : SubEnum Y) :
  free_omega_qlift (fun x y => edge x y)
    (sample X mu) (sample Y nu) ->
  exists joint : SubEnum (X * Y),
    @semantic_coupling SubEnum SubEnum_SemanticMeasure X Y
      (fun x y => edge x y) mu nu joint.
Proof.
  intro Hq. apply subenum_finite_transport_joint.
  - intro S.
    have Hf : forall x : X, 0 <= (if x \in S then 1 else 0 : rat) /\
      (if x \in S then 1 else 0 : rat) <= 1.
    { intro x. case: (x \in S); split; try exact: ler01; exact: lexx. }
    have Hg : forall y : Y, 0 <= (if y \in matching_neighbors edge setT S then 1 else 0 : rat) /\
      (if y \in matching_neighbors edge setT S then 1 else 0 : rat) <= 1.
    { intro y. case: (y \in matching_neighbors edge setT S); split; try exact: ler01; exact: lexx. }
    have Hfg : forall x y, edge x y ->
      (if x \in S then 1 else 0 : rat) <=
      (if y \in matching_neighbors edge setT S then 1 else 0 : rat).
    { intros x y Hxy. case Hx: (x \in S).
      - have Hy : y \in matching_neighbors edge setT S.
        { apply/matching_neighborsP. split; [by rewrite inE|]. exists x. by split. }
        by rewrite Hy.
      - case: (y \in matching_neighbors edge setT S); [exact: ler01|exact: lexx]. }
    have H := subenum_quotient_rational_tests Hq Hf Hg Hfg.
    rewrite !finite_enum_expect in H.
    have Hind : forall (I : finType) (weights : I -> rat) (P : pred I),
      (\sum_i weights i * (if P i then 1 else 0)) = \sum_(i | P i) weights i.
    { intros I weights P. rewrite [RHS]big_mkcond. apply eq_bigr=> i _.
      by case: (P i); rewrite ?mulr0 ?mulr1. }
    by rewrite !Hind in H.
  - have H := subenum_quotient_equal_mass Hq.
    unfold enum_mass in H. rewrite !finite_enum_expect in H.
    have Hone : forall (I : finType) (w : I -> rat), (\sum_i w i * 1) = \sum_i w i.
    { intros I w. apply eq_bigr=> i _. exact: mulr1. }
    by rewrite !Hone in H.
Qed.

End FiniteCarrier.

Definition subenum_finite_presentation {A}
    (p : free_omega_native_presentation SubEnum A) : free_omega_native_presentation SubEnum A :=
  {| native_sample_type := enum_position (subenum_raw (native_sample_measure p));
     native_sample_measure := subenum_positions (native_sample_measure p);
     native_sample_value := fun i => native_sample_value p
       (enum_position_value (subenum_raw (native_sample_measure p)) i) |}.

Lemma subenum_finite_presentation_correct {A}
    (p : free_omega_native_presentation SubEnum A) :
  free_omega_qlift eq (free_omega_native (subenum_finite_presentation p)) (free_omega_native p).
Proof.
  eapply FOQLSample; [apply subenum_positions_decode|].
  intros i x Hix. apply FOQLStructural, FOLRet.
  cbn. by rewrite Hix.
Qed.

(** Arbitrary result relations and noninjective higher-universe decoders
    are permitted.  The finite carrier is only a proof device; the result
    couples the ORIGINAL native sample measures. *)
Theorem subenum_native_quotient_coupling {A B}
    (p : free_omega_native_presentation SubEnum A)
    (q : free_omega_native_presentation SubEnum B) (T : A -> B -> Prop) :
  free_omega_qlift T (free_omega_native p) (free_omega_native q) ->
  exists joint : SubEnum (native_sample_type p * native_sample_type q),
    @semantic_coupling SubEnum SubEnum_SemanticMeasure _ _
      (fun x y => T (native_sample_value p x) (native_sample_value q y))
      (native_sample_measure p) (native_sample_measure q) joint.
Proof.
  intro Hq.
  pose (fp := subenum_finite_presentation p).
  pose (fq := subenum_finite_presentation q).
  have Hfinite : free_omega_qlift T (free_omega_native fp) (free_omega_native fq).
  { eapply FOQLComp with (T := eq) (U := T).
    - exact (subenum_finite_presentation_correct p).
    - eapply FOQLComp with (T := T) (U := fun x y => y = x).
      + exact Hq.
      + apply FOQLSym. exact (subenum_finite_presentation_correct q).
      + intros x z [y [Hxy <-]]. exact Hxy.
    - intros x z [y [-> Hyz]]. exact Hyz. }
  have Hpull := subenum_native_coupling_pullback Hfinite.
  pose (edge := fun i j => if excluded_middle_informative
    (T (native_sample_value fp i) (native_sample_value fq j)) then true else false).
  have Hedge : forall i j, edge i j <-> T (native_sample_value fp i) (native_sample_value fq j).
  { intros i j. unfold edge. destruct (excluded_middle_informative
      (T (native_sample_value fp i) (native_sample_value fq j))) as [Hyes|Hno].
    - split; [intros _; exact Hyes|intros _; reflexivity].
    - split; [intro Hfalse; discriminate Hfalse|intro Hbad; contradiction]. }
  have Hbool : free_omega_qlift (fun i j => edge i j)
    (FOSample (native_sample_measure fp) FORet) (FOSample (native_sample_measure fq) FORet).
  { eapply FOQLMono; [exact Hpull|]. intros i j Hij. exact (proj2 (Hedge i j) Hij). }
  destruct (subenum_finite_quotient_joint (Anchor := (A * B)%type) Hbool)
    as [indexed_joint Hjoint].
  have Hlift := @semantic_coupling_sound SubEnum SubEnum_SemanticMeasure
    SubEnum_SemanticMeasureCoreLaws SubEnum_SemanticMeasureCouplingAELaws _ _ _ _ _ _ Hjoint.
  apply subenum_coupling_realization.
  eapply sem_lift_mono with (R := fun x y => exists i,
    enum_position_value (subenum_raw (native_sample_measure p)) i = x /\
    exists j, edge i j /\ enum_position_value (subenum_raw (native_sample_measure q)) j = y).
  - intros x y [i [<- [j [Hij <-]]]]. exact (proj1 (Hedge i j) Hij).
  - eapply sem_lift_comp.
    + apply sem_lift_sym. apply subenum_positions_decode.
    + eapply sem_lift_comp; [exact Hlift|apply subenum_positions_decode].
Qed.
End NativeTransport.
