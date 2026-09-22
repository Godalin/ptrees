(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import ClassicalChoice FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool seq ssralg ssrnum rat.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.EnumQ.Iteration PTree.Prob.Backend.EnumQ.Representation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).

(** Forgetting an observation's value preserves its mass. This is a
    concrete backend fact, not an axiom about abstract [sem_total]. *)
Lemma subenumQ_observes_unit {A O} (obs : A -> O) mu out :
  @free_omega_observes SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    A O obs mu out ->
  exists unit_out,
    @free_omega_observes SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
      A unit (fun _ => tt) mu unit_out /\
    enumQ_mass (subenumQ_raw unit_out) = enumQ_mass (subenumQ_raw out).
Proof.
  intro Hobs. induction Hobs.
  - exists (subenumQ_ret tt). split; [constructor|].
    reflexivity.
  - exists (@subenumQ_zero unit). split; [constructor|reflexivity].
  - destruct (choice _ H0) as [front' Hfront].
    exists (subenumQ_bind mu front'). split.
    + apply (FOOObserveSample (NI := SubEnumQ_SemanticMeasure)).
      intro x. exact (proj1 (Hfront x)).
    + change (enumQ_expect (fun _ => 1) (bind_EnumQ (subenumQ_raw mu)
        (fun x => subenumQ_raw (front' x))) =
        enumQ_expect (fun _ => 1) (bind_EnumQ (subenumQ_raw mu)
        (fun x => subenumQ_raw (front x)))).
      rewrite !enumQ_expect_bind.
      have Heq : (fun x => enumQ_mass (subenumQ_raw (front' x))) =
        (fun x => enumQ_mass (subenumQ_raw (front x))).
      { apply functional_extensionality. intro x. exact (proj2 (Hfront x)). }
      change (enumQ_expect (fun x => enumQ_mass (subenumQ_raw (front' x))) (subenumQ_raw mu) =
        enumQ_expect (fun x => enumQ_mass (subenumQ_raw (front x))) (subenumQ_raw mu)).
      rewrite Heq. reflexivity.
  - destruct (choice _ H0) as [outs' Houts].
    exists (subenumQ_bind out (fun _ => subenumQ_ret tt)). split.
    + eapply FOOObserveLub with (outs := outs').
      * intro n. exact (proj1 (Houts n)).
      * change (enumQ_converges (fun n => subenumQ_raw (outs' n))
          (bind_EnumQ (subenumQ_raw out) (fun _ => ret_EnumQ tt))).
        intros P eps Heps.
        destruct (H1 (fun _ => P tt) eps Heps) as [N HN].
        exists N. intros n Hn. specialize (HN n Hn).
        have HPconst : (fun x : unit => if P x then (1 : rat) else 0) =
          (fun _ : unit => if P tt then 1 else 0).
        { apply functional_extensionality. intros []. reflexivity. }
        rewrite HPconst enumQ_expect_bind.
        rewrite enumQ_expect_ret.
        destruct (P tt) eqn:HP.
        -- change (`|enumQ_mass (subenumQ_raw (outs' n)) -
             enumQ_mass (subenumQ_raw out)| < eps).
           rewrite (proj2 (Houts n)). exact HN.
        -- have Hz : forall (T : Type) (mu : EnumQ T), enumQ_expect (fun _ => 0) mu = 0.
           { intros T m. exact: finite_expect_zero. }
           rewrite !Hz subrr normr0. exact Heps.
      * exact H2.
    + change (enumQ_expect (fun _ => 1) (bind_EnumQ (subenumQ_raw out)
        (fun _ => ret_EnumQ tt)) = enumQ_mass (subenumQ_raw out)).
      rewrite enumQ_expect_bind enumQ_expect_ret.
      reflexivity.
Qed.

(** Observable totality is functorial on this backend. The proof changes
    the totality witness to the constant unit observation BEFORE mapping;
    no inverse of [f], separation, or injectivity is needed. *)
Theorem subenumQ_free_omega_total_map {A B} (f : A -> B) mu :
  @sem_total (FreeOmega SubEnumQ) FI FO A mu ->
  @sem_total (FreeOmega SubEnumQ) FI FO B
    (free_omega_bind mu (fun x => FORet (f x))).
Proof.
  intros [rep [Heq [O [obs [out [Hobs Htotal]]]]]].
  destruct (subenumQ_observes_unit Hobs) as [out' [Hunit Hmass]].
  exists (free_omega_bind rep (fun x => FORet (f x))). split.
  - eapply FOQLBind; [exact Heq|].
    intros x y ->. apply (sem_eq_refl (SI := FI)).
  - exists unit, (fun _ => tt), out'. split.
    + eapply free_omega_observes_bind_ret; [exact Hunit|reflexivity].
    + change (enumQ_mass (subenumQ_raw out') = 1).
      rewrite Hmass. exact Htotal.
Qed.
