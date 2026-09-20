Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Logic.ClassicalDescription Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype
  finset bigop ssralg ssrnum order rat reals.
From mathcomp.analysis Require Import ereal.
From PTree.Prob Require Import RatSubTypes DiscreteMC MeasureIterationEnum EnumSupport
  TwoLevelMeasure TwoLevelMeasureEnum SemanticCoupling SemanticCouplingEnum Coupling
  FiniteMatching FiniteRationalTransport FiniteEnumTransport FiniteEnumPresentation
  FreeOmegaMeasure FreeOmegaNative FreeOmegaUpperExpectationEnum
  FreeOmegaUpperRelationalEnum FreeOmegaUpperQuotientEnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum Coupling GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section NativeTransport.
Variable F : realType.

(** These tests apply to the DECODED values, possibly in a higher universe.
    Neither injectivity of the decoders nor a conditional kernel is needed. *)
Lemma enum_decoded_quotient_rational_tests {A B X Y}
    (T : A -> B -> Prop) (mu : Enum X) (nu : Enum Y)
    (decode : X -> A) (decode' : Y -> B) f g :
  free_omega_qlift T (FOSample mu (fun x => FORet (decode x)))
    (FOSample nu (fun y => FORet (decode' y))) ->
  (forall x, 0 <= f x) -> (forall y, 0 <= g y) ->
  (forall x y, T x y -> f x <= g y) ->
  enum_expect (fun x => f (decode x)) mu <= enum_expect (fun y => g (decode' y)) nu.
Proof.
  intros Hq Hf Hg Hfg.
  have Hf' : nonnegative_test (fun x => (ratr (f x) : F)%:E).
  { intro x. rewrite lee_fin ler0q. exact (Hf x). }
  have Hg' : nonnegative_test (fun y => (ratr (g y) : F)%:E).
  { intro y. rewrite lee_fin ler0q. exact (Hg y). }
  have Hfg' : forall x y, T x y -> ((ratr (f x) : F)%:E <= (ratr (g y))%:E)%E.
  { intros x y Hxy. rewrite lee_fin ler_rat. exact (Hfg x y Hxy). }
  have H := free_omega_qlift_extended_upper Hq Hf' Hg' Hfg'.
  change (is_true (enum_extended_expect (fun x => (ratr (f (decode x)) : F)%:E) mu <=
    enum_extended_expect (fun y => (ratr (g (decode' y)) : F)%:E) nu)%E) in H.
  (* Fix both the native-carrier and scalar universes.  Leaving the latter
     implicit here makes Coq 8.20 elaborate a phantom universe differently
     in the rewrite proof; it then fails kernel checking at Qed. *)
  rewrite (@enum_extended_expect_rat@{DiscreteMC.Enum.Enum.u0 constructive_ereal.adde_ge0.u1}
    F X (fun x => f (decode x)) mu) in H.
  rewrite (@enum_extended_expect_rat@{DiscreteMC.Enum.Enum.u0 constructive_ereal.adde_ge0.u1}
    F Y (fun y => g (decode' y)) nu) in H.
  by rewrite lee_fin ler_rat in H.
Qed.

Lemma enum_decoded_quotient_equal_mass {A B X Y}
    (T : A -> B -> Prop) (mu : Enum X) (nu : Enum Y)
    (decode : X -> A) (decode' : Y -> B) :
  free_omega_qlift T (FOSample mu (fun x => FORet (decode x)))
    (FOSample nu (fun y => FORet (decode' y))) ->
  enum_expect (fun _ => 1) mu = enum_expect (fun _ => 1) nu.
Proof.
  intro Hq. have H := free_omega_qlift_extended_upper_mass F Hq.
  change (enum_extended_expect (fun _ => (1 : \bar F)%E) mu =
    enum_extended_expect (fun _ => (1 : \bar F)%E) nu) in H.
  rewrite !enum_extended_expect_one in H. injection H as Hr.
  exact (fmorph_inj (ratr : {rmorphism rat -> F}) Hr).
Qed.

(** Hall's source test saturates a selected finite set under the decoder.
    It may overcount the source set, which is harmless for the inequality;
    its related target test is EXACTLY the neighbor-set indicator.  This
    avoids requiring an inverse or a disintegration of either decoder. *)
Theorem enum_finite_decoded_quotient_coupling {A B} {X Y : finType}
    (T : A -> B -> Prop) (mu : Enum X) (nu : Enum Y)
    (decode : X -> A) (decode' : Y -> B) (edge : X -> Y -> bool)
    (Hedge : forall x y, edge x y <-> T (decode x) (decode' y)) :
  free_omega_qlift T (FOSample mu (fun x => FORet (decode x)))
    (FOSample nu (fun y => FORet (decode' y))) ->
  coupling (fun x y => edge x y) mu nu.
Proof.
  intro Hq. apply finite_enum_transport.
  - intro S.
    pose f (a : A) : rat := if excluded_middle_informative
      (exists x : X, x \in S /\ decode x = a) then 1 else 0.
    pose g (b : B) : rat := if excluded_middle_informative
      (exists x : X, x \in S /\ T (decode x) b) then 1 else 0.
    have Hf : forall a, 0 <= f a.
    { intro a. unfold f. destruct (excluded_middle_informative _); [exact: ler01|exact: lexx]. }
    have Hg : forall b, 0 <= g b.
    { intro b. unfold g. destruct (excluded_middle_informative _); [exact: ler01|exact: lexx]. }
    have Hfg : forall a b, T a b -> f a <= g b.
    { intros a b Hab. unfold f, g.
      destruct (excluded_middle_informative (exists x : X, x \in S /\ decode x = a))
        as [[x [Hx Hxa]]|Hnone].
      - destruct (excluded_middle_informative (exists x : X, x \in S /\ T (decode x) b))
          as [Hyes|Hno]; [exact: lexx|].
        exfalso. apply Hno. exists x. split; [exact Hx|by rewrite Hxa].
      - destruct (excluded_middle_informative _); [exact: ler01|exact: lexx]. }
    have Hleft : enum_expect (fun x => if x \in S then 1 else 0) mu <=
        enum_expect (fun x => f (decode x)) mu.
    { apply enum_expect_mono=> x. case Hx: (x \in S); last exact: Hf.
      unfold f. destruct (excluded_middle_informative _) as [Hyes|Hno]; [exact: lexx|].
      exfalso. apply Hno. exists x. split; [exact Hx|reflexivity]. }
    have Hright : (fun y => g (decode' y)) =
        (fun y => if y \in matching_neighbors edge setT S then 1 else 0).
    { apply functional_extensionality=> y. unfold g.
      destruct (excluded_middle_informative _) as [[x [Hx Hxy]]|Hnone].
      - have Hy : y \in matching_neighbors edge setT S.
        { apply/matching_neighborsP. split; [by rewrite inE|].
          exists x. split; [exact Hx|exact (proj2 (Hedge x y) Hxy)]. }
        by rewrite Hy.
      - case Hy: (y \in matching_neighbors edge setT S); [|reflexivity].
        exfalso. apply Hnone. move/matching_neighborsP: Hy=> [_ [x [Hx Hxy]]].
        exists x. split; [exact Hx|exact (proj1 (Hedge x y) Hxy)]. }
    have Hcompare := enum_decoded_quotient_rational_tests Hq Hf Hg Hfg.
    have H := le_trans Hleft Hcompare. rewrite Hright !finite_enum_expect in H.
    have Hind : forall (I : finType) (w : I -> rat) (P : pred I),
      (\sum_i w i * (if P i then 1 else 0)) = \sum_(i | P i) w i.
    { intros I w P. rewrite [RHS]big_mkcond. apply eq_bigr=> i _.
      by case: (P i); rewrite ?mulr0 ?mulr1. }
    by rewrite !Hind in H.
  - have H := enum_decoded_quotient_equal_mass Hq.
    rewrite !finite_enum_expect in H.
    have Hone : forall (I : finType) (w : I -> rat), (\sum_i w i * 1) = \sum_i w i.
    { intros I w. apply eq_bigr=> i _. exact: mulr1. }
    by rewrite !Hone in H.
Qed.

Definition enum_finite_presentation {A}
    (p : free_omega_native_presentation Enum A) : free_omega_native_presentation Enum A :=
  {| native_sample_type := enum_position (native_sample_measure p);
     native_sample_measure := enum_positions (native_sample_measure p);
     native_sample_value := fun i => native_sample_value p
       (enum_position_value (native_sample_measure p) i) |}.

Lemma enum_positions_lift_decode {A} (mu : Enum A) :
  sem_lift (fun i x => enum_position_value mu i = x) (enum_positions mu) mu.
Proof.
  have H := enum_lift_decode (enum_positions mu) (enum_position_value mu).
  rewrite enum_positions_decode in H. exact H.
Qed.

Lemma enum_finite_presentation_correct {A} (p : free_omega_native_presentation Enum A) :
  free_omega_qlift eq (free_omega_native (enum_finite_presentation p)) (free_omega_native p).
Proof.
  eapply FOQLSample; [apply enum_positions_lift_decode|].
  intros i x Hix. apply FOQLStructural, FOLRet. cbn. by rewrite Hix.
Qed.

Theorem enum_native_quotient_coupling {A B}
    (p : free_omega_native_presentation Enum A)
    (q : free_omega_native_presentation Enum B) (T : A -> B -> Prop) :
  free_omega_qlift T (free_omega_native p) (free_omega_native q) ->
  exists joint : Enum (native_sample_type p * native_sample_type q),
    @semantic_coupling Enum Enum_SemanticMeasure _ _
      (fun x y => T (native_sample_value p x) (native_sample_value q y))
      (native_sample_measure p) (native_sample_measure q) joint.
Proof.
  intro Hq. pose fp := enum_finite_presentation p. pose fq := enum_finite_presentation q.
  have Hfinite : free_omega_qlift T (free_omega_native fp) (free_omega_native fq).
  { eapply FOQLComp with (T := eq) (U := T).
    - exact (enum_finite_presentation_correct p).
    - eapply FOQLComp with (T := T) (U := fun x y => y = x).
      + exact Hq.
      + apply FOQLSym. exact (enum_finite_presentation_correct q).
      + intros x z [y [Hxy <-]]. exact Hxy.
    - intros x z [y [-> Hyz]]. exact Hyz. }
  pose edge i j := if excluded_middle_informative
    (T (native_sample_value fp i) (native_sample_value fq j)) then true else false.
  have Hedge : forall i j, edge i j <-> T (native_sample_value fp i) (native_sample_value fq j).
  { intros i j. unfold edge. destruct (excluded_middle_informative _) as [Hyes|Hno].
    - split; [intros _; exact Hyes|intros _; reflexivity].
    - split; [intro Hfalse; discriminate Hfalse|intro Hbad; contradiction]. }
  have Hjoint := enum_finite_decoded_quotient_coupling Hedge Hfinite.
  have Hlift := enum_sem_lift_of_coupling Hjoint.
  apply enum_coupling_realization.
  eapply sem_lift_mono with (R := fun x y => exists i,
    enum_position_value (native_sample_measure p) i = x /\
    exists j, edge i j /\ enum_position_value (native_sample_measure q) j = y).
  - intros x y [i [<- [j [Hij <-]]]]. exact (proj1 (Hedge i j) Hij).
  - eapply sem_lift_comp.
    + apply sem_lift_sym. apply enum_positions_lift_decode.
    + eapply sem_lift_comp; [exact Hlift|apply enum_positions_lift_decode].
Qed.
End NativeTransport.
