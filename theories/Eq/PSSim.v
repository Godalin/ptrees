(** Probabilistic Strong Simulation Relation *)
Set Warnings "-ambiguous-paths".
Unset Universe Checking.

Require Import Utf8.
Require Import Program Morphisms.

From Coinduction Require Import all.
From RelationAlgebra Require Import rel srel.
From mathcomp Require Import ssreflect ssrbool eqtype seq finset ssralg order.

From PTree.Core Require Import PTreeDefinitionNew Utils.
From PTree.Prob Require Import RatSubTypes DiscreteMC.
From PTree.Eq Require Import ShallowNew EquNew Trans.



Section PSSim.
Import Enum.
Import NonnegQNotations.
Import GRing.Theory Order.Theory.
Import EquNotations.

#[local] Notation ptree E := (ptree E Enum).
#[local] Notation ptree' E R := (ptree' E Enum R).

Fixpoint transAll {E X} α (t : ptree E X)
    (tlist : list (ℚ≥0 * ptree E X)) : Prop :=
  match tlist with
  | [::] => True
  | (p, t') :: tlist' => trans α p t t' ∧ transAll α t tlist'
  end.

Fixpoint transAllPrb {E X} (tlist : Enum (ptree E X)) : ℚ≥0 :=
  match tlist with
  | [::] => 0
  | (p, t') :: tlist' => p + transAllPrb tlist'
  end.

Fixpoint relateAll {X Y} (R : rel X Y) (x : X) (ys : list Y) : Prop :=
  match ys with
  | [::] => True
  | y :: ys' => R x y ∧ relateAll R x ys'
  end.

Lemma sub_relateAll {X Y} (R S : rel X Y) (x : X) (ys : list Y)
  : (∀ x y, R x y → S x y) → relateAll R x ys → relateAll S x ys.
Proof. elim: ys => [//|y ys IH //= H] [Hxy Hxys]. auto. Qed.

Definition mass {X : eqType} (μ : Enum X) (s : seq X) : ℚ≥0
  := foldr (λ x acc, acc_mass x μ + acc) 0 s.

Definition enumk {Y} {X : eqType} (μ : Enum X) (k : X → Y) (x : X) : ℚ≥0 * Y
  := (acc_mass x μ, k x).


Section experiment.
Context {E F : Type → Type} {X Y : Type}.

(* Old definitions of [pss], probabilistic strong simulation.
  This version has the problem of not being unique in the provided
  [seq] of [weight * ptree]. *)

(* #[program] *)
(* Definition pss {E F : Type → Type} *)
(*     {X Y : Type} (L : rel (@label E) (@label F)) *)
(*   : mon (ptree E X → ptree F Y → Prop) *)
(*   := {| body R t u := ∀ l p t', *)
(*         trans l p t t' → *)
(*           ∃ l' (u's : list (ℚ≥0 * ptree F Y)), *)
(*             transAll l' u u's *)
(*             ∧ p <= (transAllPrb u's) *)
(*             ∧ relateAll R t' (map snd u's) *)
(*             ∧ L l l' |}. *)
(* Next Obligation. *)
(* Admitted. *)

(* #[program] *)
(* Definition pss' {E F : Type → Type} *)
(*     {X Y : Type} (L : rel (@label E) (@label F)) *)
(*   : mon (ptree E X → ptree F Y → Prop) *)
(*   := {| body R t u := ∀ l (p : ℚ≥0) t', *)
(*         trans l p t t' → *)
(*           ∃ l' (X' : eqType) (k' : X' → ℚ≥0 * ptree F Y) (x's : seq X'), *)
(*             uniq x's *)
(*             ∧ let u's := [seq k' x | x <- x's] in *)
(*               transAll l' u u's *)
(*               ∧ p <= (transAllPrb u's) *)
(*               ∧ relateAll R t' (map snd u's) *)
(*               ∧ L l l' |}. *)
(* Next Obligation. *)
(* move: (H0 l p t' H1) => *)
(*   [l' [X' [k' [x's [Huniq [Htrans [Hprob [Hrelate HL]]]]]]]]. *)
(* exists l', X', k', x's. repeat (split; auto). *)
(* apply: sub_relateAll. apply H. auto. *)
(* Defined. *)

(** Goal: define a prop: [R t u] is a simulation, or part of the prop
    t -- R ---- u
    |         | | |
  l |         p q r l
    |         | | |
    v         v v v
    t'-- R -- u'u'u'
  *)

Variant pssim_cond REL (t' : ptree E X) (l' : label) (p : ℚ≥0)
  : ptree' F Y → Prop :=
  | PSSimRetF
    : ∀ r u',
        trans l' p (Ret r) u'
      → REL t' u'
      → pssim_cond REL t' l' p (RetF r)
  | PSSimTauF
    : ∀ t u',
        trans l' p (Tau t) u'
      → REL t' u'
      → pssim_cond REL t' l' p (TauF t)
  | PSSimVisF
    : ∀ X' (e : F X') k u',
        trans l' p (Vis e k) u'
      → REL t' u'
      → pssim_cond REL t' l' p (VisF e k)
  | PSSimProbF
    : ∀ (X' : eqType) (μ : Enum X') (k : X' → ptree F Y) (s : seq X'),
        subseq s (supp μ)
      → transAll l' (Prob μ k) [seq enumk μ k x | x <- s]
      → relateAll REL t' [seq k x | x <- s]
      → p <= mass μ s
      → pssim_cond REL t' l' p (ProbF μ k).

(* Variant pssim_cond REL (t' : ptree E X) (l' : label) (p : ℚ≥0) *)
(*   : ptree' F Y → Prop := *)
(*   | PSSimTrans' *)
(*     : ∀ u u', *)
(*         trans l' p u u' *)
(*       → pssim_cond REL t' l' p (observe u) *)
(*   | PSSimProbF' *)
(*     : ∀ (X' : eqType) (μ : Enum X') (k : X' → ptree F Y) (s : seq X'), *)
(*         subseq s (supp μ) *)
(*       → transAll l' (Prob μ k) [seq enumk μ k x | x <- s] *)
(*       → relateAll REL t' [seq k x | x <- s] *)
(*       → p <= mass μ s *)
(*       → pssim_cond REL t' l' p (ProbF μ k). *)

Lemma sub_pssim_cond (R S : rel (ptree E X) (ptree F Y))
    t' (l : @label F) p u
  : (∀ x y, R x y → S x y) → pssim_cond R t' l p u → pssim_cond S t' l p u.
Proof. intros. inversion H0.
  - econstructor. apply H1. auto.
  - econstructor. apply H1. auto.
  - econstructor. apply H1. auto.
  - econstructor. apply H1. all: auto.
    apply (sub_relateAll R S); auto.
Qed.

Lemma pssim_cond_char : ∀ (REL : rel (ptree E X) (ptree F Y)) t' l p u,
    pssim_cond REL t' l p u
  → ∃ (u's : Enum (ptree F Y)),
      transAll l (go u) u's
    ∧ relateAll REL t' [seq snd p | p <- u's]
    ∧ p <= transAllPrb u's.
Proof. intros REL t' l p u H. inversion H; subst.
  - exists [:: (p, u')]; repeat split; simpl.
    inversion H0; subst; auto. assumption.
    rewrite addr0. rewrite le_refl. auto.
  - exists [:: (p, u')]; repeat split; simpl.
    inversion H0; subst; auto. assumption.
    rewrite addr0. rewrite le_refl. auto.
  - exists [:: (p, u')]; repeat split; simpl.
    inversion H0; subst. dependent destruction H7.
    econstructor. rewrite -> H5. apply observe_equ_eq.
    assumption. assumption.
    rewrite addr0. rewrite le_refl. auto.
  - exists (map (enumk μ k) s); repeat split; simpl.
    apply H1.
Admitted.



End experiment.

(** [pss] is the monotone function for probabilistic strong simulation  *)

#[program]
Definition pss {E F : Type → Type}
    {X Y : Type} (L : rel (@label E) (@label F))
  : mon (ptree E X → ptree F Y → Prop)
  := {| body R t u := ∀ l (p : ℚ≥0) t',
        trans l p t t' → ∃ l',
          L l l' ∧ pssim_cond R t' l' p (observe u)
     |}.
Next Obligation.
  destruct (H0 l p t' H1) as [l' [RL HCond]].
  exists l'. split; auto. apply (sub_pssim_cond x y); auto.
Defined.

(** [pssim] is the probabilistic similarity, which is defined as
    the greatest fixpoint of the monotone function [pss] *)

Definition pssim {E F X Y} L := (gfp (@pss E F X Y L)).

End PSSim.



(** pss notation *)
Module Import PSSimNotations.
Notation "` R" := (elem R) (at level 10).

Infix "≲p" := (pssim eq) (at level 70).
Infix "(≲p  L )" := (pssim L) (at level 70).

Notation psst L := (` (_ : Chain (pss L))).
Notation pssbt L := (pssim L (` (_ : Chain (pss L)))).

Infix "[≲p  L ]" := (pss L _) (at level 70).
Infix "[≲p]" := (pss eq _) (at level 70).
Infix "{≲p  L }" := (psst L _) (at level 70).
Infix "{≲p}" := (psst eq _) (at level 70).
Infix "{{≲p  L }}" := (pssbt L _) (at level 70).
Infix "{{≲p}}" := (pssbt eq _) (at level 70).

End PSSimNotations.



Ltac __step_pssim := step.
#[local] Tactic Notation "step" := __step_pssim.

Ltac __step_in_pssim H :=
  match type of H with
  | context [@pssim ?E ?X ?Y _ _ ?RL] =>
      unfold pssim in H
  end.



Section homogenous_pssim_theory.
Import Enum.
Import GRing.Theory Order.Theory.
Import NonnegQNotations.
Import EquNotations.
#[local] Notation ptree E := (ptree E Enum).

Context {E : Type → Type} {X : Type}.
Context {L : relation (@label E)}.

#[global]
Instance Reflexive_pss {RC : relation (ptree E X)}
    `{Reflexive _ L} `{Reflexive _ RC}
  : Reflexive (pss L RC).
Proof. cbn. intros. inversion H1. 
  - exists tau. split. reflexivity. eapply PSSimTauF. eapply StepTau. reflexivity. admit.
  - exists (obs e x0). split. reflexivity. eapply PSSimVisF. eapply StepObs. reflexivity. admit.
  - exists (val r). split. reflexivity. apply (PSSimRetF RC t' (val r) 1 r (Prob0 μ k)). eapply StepVal. admit.
  - exists tau. split. reflexivity. apply (PSSimProbF RC t' tau p X0 μ k (supp μ)).
    auto. elim: (supp μ) => [//|head tail ih]. rewrite map_cons. rewrite //=. split.
    eapply StepPrb. reflexivity. reflexivity. by [].
    unfold transR in H1. elim: (supp μ) => [//|head tail ih]. rewrite map_cons. rewrite //=. split.
    admit. exact ih. rewrite <- H6. unfold disc_mass. rewrite //=. admit.
Admitted.

#[global]
Instance Reflexive_hpssim `{Reflexive _ L} (RC : Chain (@pss E E X X L))
  : Reflexive (` RC).
Proof. revert RC. apply Reflexive_chain.
  intros RC HRC.
Admitted.

End homogenous_pssim_theory.
