Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import ClassicalChoice FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool seq ssralg ssrnum rat.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum
  FreeOmegaMeasure MeasureIterationEnum DiscreteMC.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).

(** Forgetting an observation's value preserves its mass. This is a
    concrete backend fact, not an axiom about abstract [sem_total]. *)
Lemma subenum_observes_unit {A O} (obs : A -> O) mu out :
  @free_omega_observes SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega
    A O obs mu out ->
  exists unit_out,
    @free_omega_observes SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega
      A unit (fun _ => tt) mu unit_out /\
    enum_mass (subenum_raw unit_out) = enum_mass (subenum_raw out).
Proof.
  intro Hobs. induction Hobs.
  - exists (subenum_ret tt). split; [constructor|].
    reflexivity.
  - exists (@subenum_zero unit). split; [constructor|reflexivity].
  - destruct (choice _ H0) as [front' Hfront].
    exists (subenum_bind mu front'). split.
    + apply (FOOObserveSample (NI := SubEnum_SemanticMeasure)).
      intro x. exact (proj1 (Hfront x)).
    + change (enum_expect (fun _ => 1) (bind_Enum (subenum_raw mu)
        (fun x => subenum_raw (front' x))) =
        enum_expect (fun _ => 1) (bind_Enum (subenum_raw mu)
        (fun x => subenum_raw (front x)))).
      rewrite !enum_expect_bind.
      have Heq : (fun x => enum_mass (subenum_raw (front' x))) =
        (fun x => enum_mass (subenum_raw (front x))).
      { apply functional_extensionality. intro x. exact (proj2 (Hfront x)). }
      change (enum_expect (fun x => enum_mass (subenum_raw (front' x))) (subenum_raw mu) =
        enum_expect (fun x => enum_mass (subenum_raw (front x))) (subenum_raw mu)).
      rewrite Heq. reflexivity.
  - destruct (choice _ H0) as [outs' Houts].
    exists (subenum_bind out (fun _ => subenum_ret tt)). split.
    + eapply FOOObserveLub with (outs := outs').
      * intro n. exact (proj1 (Houts n)).
      * change (enum_converges (fun n => subenum_raw (outs' n))
          (bind_Enum (subenum_raw out) (fun _ => ret_Enum tt))).
        intros P eps Heps.
        destruct (H1 (fun _ => P tt) eps Heps) as [N HN].
        exists N. intros n Hn. specialize (HN n Hn).
        have HPconst : (fun x : unit => if P x then (1 : rat) else 0) =
          (fun _ : unit => if P tt then 1 else 0).
        { apply functional_extensionality. intros []. reflexivity. }
        rewrite HPconst enum_expect_bind.
        rewrite enum_expect_ret.
        destruct (P tt) eqn:HP.
        -- change (`|enum_mass (subenum_raw (outs' n)) -
             enum_mass (subenum_raw out)| < eps).
           rewrite (proj2 (Houts n)). exact HN.
        -- have Hz : forall (T : Type) (mu : Enum T), enum_expect (fun _ => 0) mu = 0.
           { intros T m. induction m as [|[p x] m IH]; [reflexivity|].
             change (RatSubTypes.Qval p * 0 + enum_expect (fun _ => 0) m = 0).
             by rewrite mulr0 IH addr0. }
           rewrite !Hz subrr normr0. exact Heps.
      * exact H2.
    + change (enum_expect (fun _ => 1) (bind_Enum (subenum_raw out)
        (fun _ => ret_Enum tt)) = enum_mass (subenum_raw out)).
      rewrite enum_expect_bind enum_expect_ret.
      reflexivity.
Qed.

(** Observable totality is functorial on this backend. The proof changes
    the totality witness to the constant unit observation BEFORE mapping;
    no inverse of [f], separation, or injectivity is needed. *)
Theorem subenum_free_omega_total_map {A B} (f : A -> B) mu :
  @sem_total (FreeOmega SubEnum) FI FO A mu ->
  @sem_total (FreeOmega SubEnum) FI FO B
    (free_omega_bind mu (fun x => FORet (f x))).
Proof.
  intros [rep [Heq [O [obs [out [Hobs Htotal]]]]]].
  destruct (subenum_observes_unit Hobs) as [out' [Hunit Hmass]].
  exists (free_omega_bind rep (fun x => FORet (f x))). split.
  - eapply FOQLBind; [exact Heq|].
    intros x y ->. apply (sem_eq_refl (SI := FI)).
  - exists unit, (fun _ => tt), out'. split.
    + eapply free_omega_observes_bind_ret; [exact Hunit|reflexivity].
    + change (enum_mass (subenum_raw out') = 1).
      rewrite Hmass. exact Htotal.
Qed.
