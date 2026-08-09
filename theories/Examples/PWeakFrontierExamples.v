Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms.

From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg order rat.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import RatSubTypes DiscreteMC EnumBindFacts
  Coupling IndexedCoupling FrontierLift FrontierLiftEnum.
From PTree.Eq Require Import PFrontier PWeak PWeakFacts PWeakAbstract.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum Coupling IndexedCoupling.
Import RatSubTypes.NonnegQNotations.
Import GRing.Theory.
#[local] Open Scope subrat_scope.
#[local] Open Scope ring_scope.

Variant demoE : Type -> Type :=
  | Emit (n : nat) : demoE unit.

Definition fair : Enum bool :=
  [:: (one_div_two, false); (one_div_two, true)].

Definition parity_head (b1 b2 : bool) : phead demoE unit :=
  PHVis (Emit (if xorb b1 b2 then 1 else 0))
    (fun _ => Ret tt).

Definition nested_heads : Enum (phead demoE unit) :=
  bind_Enum fair (fun b1 =>
    bind_Enum fair (fun b2 =>
      ret_Enum (parity_head b1 b2))).

Definition pair_measure : Enum (bool * bool) :=
  bind_Enum fair (fun b1 =>
    bind_Enum fair (fun b2 =>
      ret_Enum (b1, b2))).

Definition flat_heads : Enum (phead demoE unit) :=
  bind_Enum pair_measure (fun bc =>
    ret_Enum (parity_head (fst bc) (snd bc))).

Lemma flat_heads_eq_nested :
  flat_heads = nested_heads.
Proof.
  rewrite /flat_heads /pair_measure.
  rewrite !bind_Enum_assoc.
  rewrite /nested_heads /ret_Enum /bind_Enum /=.
  by rewrite !mulr1.
Qed.

Definition nested_probability_program : ptree demoE Enum unit :=
  Prob fair (fun b1 =>
    Tau (Prob fair (fun b2 =>
      Vis (Emit (if xorb b1 b2 then 1 else 0))
        (fun _ => Ret tt)))).

Definition flattened_probability_program : ptree demoE Enum unit :=
  Tau (Prob pair_measure (fun bc =>
    Vis (Emit
      (if xorb (fst bc) (snd bc) then 1 else 0))
      (fun _ => Ret tt))).

Lemma nested_program_frontier :
  pfrontier (observe nested_probability_program) nested_heads.
Proof.
  apply PFProb=> b1.
  apply PFTau.
  apply PFProb=> b2.
  constructor.
Qed.

Lemma flat_program_frontier :
  pfrontier (observe flattened_probability_program) flat_heads.
Proof.
  apply PFTau.
  apply PFProb=> [[b1 b2]].
  constructor.
Qed.

Lemma parity_heads_reflexive :
  Reflexive
    (phead_rel eq
      (@pweak demoE unit unit eq)).
Proof.
  move=> h.
  destruct h as [r|X e k].
  - constructor. reflexivity.
  - constructor=> x. apply pweak_refl.
Qed.

(**
  The left program has two nested probabilistic nodes; the right program has
  one probabilistic node over pairs.  Their Tau placement is also different.
  Both finite probability/Tau prefixes are collapsed to the same distribution
  of [Emit] observations before the coinductive continuations are compared.
*)
Lemma nested_and_flattened_programs_equivalent :
  pweak eq nested_probability_program flattened_probability_program.
Proof.
  apply pweak_fold.
  eapply PWFrontier
    with (hs1 := nested_heads) (hs2 := flat_heads).
  - exact nested_program_frontier.
  - exact flat_program_frontier.
  - rewrite flat_heads_eq_nested.
    apply indexed_coupling_refl.
    exact parity_heads_reflexive.
Qed.

CoFixpoint weak_spin {R} : ptree demoE Enum R :=
  Tau weak_spin.

Lemma observe_weak_spin {R} :
  observe (@weak_spin R) = TauF weak_spin.
Proof. reflexivity. Qed.

Lemma weak_spin_has_no_frontier {R} hs :
  ~ pfrontier (TauF (@weak_spin R)) hs.
Proof.
  move=> H.
  remember (TauF (@weak_spin R)) as ot eqn:Hot in H.
  induction H as
      [r | X e k | t hs Hfront IH
       | X mu k front Hfronts IHs];
      try discriminate.
  apply IH.
  inversion Hot; subst t.
  exact observe_weak_spin.
Qed.

Lemma pweakF_spin_ret_absurd {R}
    (sim : ptree demoE Enum R -> ptree demoE Enum R -> Prop) r :
  pweakF eq sim (TauF weak_spin) (RetF r) -> False.
Proof.
  move=> H.
  remember (TauF (@weak_spin R)) as lhs eqn:Hlhs in H.
  remember (RetF r) as rhs eqn:Hrhs in H.
  induction H as
      [ot1 ot2 hs1 hs2 Hfront1 Hfront2 Hcouple
       | t1 t2 Hsim
       | X Y mu nu k1 k2 Hcouple
       | t1 ot2 Hinner IH
       | ot1 t2 Hinner IH];
      try discriminate.
  - subst ot1 ot2.
    exact: weak_spin_has_no_frontier Hfront1.
  - apply IH.
    + inversion Hlhs; subst t1.
      exact observe_weak_spin.
    + exact Hrhs.
Qed.

Lemma weak_spin_not_ret {R} (r : R) :
  ~ pweak eq (@weak_spin R) (Ret r).
Proof.
  move=> H.
  move: (pweak_unfold H).
  rewrite observe_weak_spin.
  exact: pweakF_spin_ret_absurd.
Qed.

(** The abstract measure-based frontier ignores a divergent branch carrying
    zero mass.  This is intentionally unprovable with the old [PFProb] rule,
    whose premise quantified over every value of the sampling type. *)
Definition live_or_zero : Enum bool :=
  [:: (1, true); (0, false)].

Definition zero_divergent_program : ptree demoE Enum unit :=
  Prob live_or_zero (fun b => if b then Ret tt else weak_spin).

Definition unit_afront (_ : bool) : Enum (aphead demoE Enum unit) :=
  ret_Enum (APHRet tt).

Lemma live_or_zero_ae_true :
  enum_ae live_or_zero (fun b => b = true).
Proof.
  move=> p b Hin Hnz.
  rewrite /live_or_zero in Hin.
  cbn in Hin.
  destruct Hin as [Hin | [Hin | []]].
  - inversion Hin. reflexivity.
  - inversion Hin. subst p b. exfalso. apply Hnz.
    apply val_inj. reflexivity.
Qed.

Lemma zero_divergent_program_has_afrontier :
  apfrontier (observe zero_divergent_program)
    (meas_bind live_or_zero unit_afront).
Proof.
  apply (APFProb (front := unit_afront)
    (Good := fun b => b = true)).
  - exact live_or_zero_ae_true.
  - move=> b ->. constructor.
Qed.

Definition parity_ahead (b1 b2 : bool) : aphead demoE Enum unit :=
  APHVis (Emit (if xorb b1 b2 then 1 else 0))
    (fun _ => Ret tt).

Definition nested_aheads : Enum (aphead demoE Enum unit) :=
  bind_Enum fair (fun b1 =>
    bind_Enum fair (fun b2 => ret_Enum (parity_ahead b1 b2))).

Definition flat_aheads : Enum (aphead demoE Enum unit) :=
  bind_Enum pair_measure (fun bc =>
    ret_Enum (parity_ahead (fst bc) (snd bc))).

Lemma flat_aheads_eq_nested : flat_aheads = nested_aheads.
Proof.
  rewrite /flat_aheads /pair_measure !bind_Enum_assoc.
  rewrite /nested_aheads /ret_Enum /bind_Enum /=.
  by rewrite !mulr1.
Qed.

Lemma nested_program_afrontier :
  apfrontier (observe nested_probability_program) nested_aheads.
Proof.
  change (apfrontier
    (ProbF fair (fun b1 =>
      Tau (Prob fair (fun b2 =>
        Vis (Emit (if xorb b1 b2 then 1 else 0))
          (fun _ => Ret tt)))))
    (meas_bind fair (fun b1 =>
      bind_Enum fair (fun b2 => ret_Enum (parity_ahead b1 b2))))).
  apply (APFProb
    (front := fun b1 =>
      bind_Enum fair (fun b2 => ret_Enum (parity_ahead b1 b2)))
    (Good := fun _ => True)).
  - apply meas_ae_true.
  - move=> b1 _. apply APFTau.
    change (apfrontier
      (ProbF fair (fun b2 =>
        Vis (Emit (if xorb b1 b2 then 1 else 0))
          (fun _ => Ret tt)))
      (meas_bind fair (fun b2 => ret_Enum (parity_ahead b1 b2)))).
    apply (APFProb
      (front := fun b2 => ret_Enum (parity_ahead b1 b2))
      (Good := fun _ => True)).
    + apply meas_ae_true.
    + move=> b2 _. constructor.
Qed.

Lemma flat_program_afrontier :
  apfrontier (observe flattened_probability_program) flat_aheads.
Proof.
  change (apfrontier
    (TauF (Prob pair_measure (fun bc =>
      Vis (Emit (if xorb (fst bc) (snd bc) then 1 else 0))
        (fun _ => Ret tt))))
    (meas_bind pair_measure (fun bc =>
      ret_Enum (parity_ahead (fst bc) (snd bc))))).
  apply APFTau.
  eapply (APFProb
    (front := fun bc =>
      ret_Enum (parity_ahead (fst bc) (snd bc)))
    (Good := fun _ => True)).
  - apply meas_ae_true.
  - move=> bc _. destruct bc as [b1 b2]. constructor.
Qed.

Lemma parity_aheads_reflexive :
  Reflexive
    (aphead_rel eq (@apweak demoE Enum
      Enum_MeasureInterface Enum_MeasureCoreLaws unit unit eq)).
Proof.
  apply aphead_rel_refl. apply apweak_refl.
Qed.

(** A genuinely non-structural equivalence for the measure-based relation:
    two nested probability nodes are equivalent to one probability node over
    pairs, despite different Tau placement and different tree shapes. *)
Lemma nested_and_flattened_programs_abstractly_equivalent :
  apweak eq nested_probability_program flattened_probability_program.
Proof.
  apply apweak_fold.
  eapply APWFrontier
    with (hs1 := nested_aheads) (hs2 := flat_aheads).
  - exact nested_program_afrontier.
  - exact flat_program_afrontier.
  - change (indexed_coupling
      (aphead_rel eq (@apweak demoE Enum
        Enum_MeasureInterface Enum_MeasureCoreLaws unit unit eq))
      (enum_prune nested_aheads) (enum_prune flat_aheads)).
    rewrite flat_aheads_eq_nested.
    apply indexed_coupling_refl.
    exact parity_aheads_reflexive.
Qed.
