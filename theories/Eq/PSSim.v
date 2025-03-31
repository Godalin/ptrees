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

Section experiment.
Context {E F : Type → Type} {X Y : Type}.

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

Lemma sub_pssim_cond (R S : rel (ptree E X) (ptree F Y))
    t' (l : @label F) p u
  : (∀ x y, R x y → S x y) → pssim_cond R t' l p u → pssim_cond S t' l p u.
Proof. intros. inversion H0.
  - econstructor. apply H1. auto.
  - econstructor. apply H1. auto.
  - econstructor. apply H1. auto.
  - econstructor. apply H1. all: auto.
    apply (relateAll_sub R S); auto.
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
    unfold transAllPrb, foldr. simpl.
    rewrite addr0. rewrite le_refl. auto.
  - exists [:: (p, u')]; repeat split; simpl.
    inversion H0; subst; auto. assumption.
    unfold transAllPrb, foldr. simpl.
    rewrite addr0. rewrite le_refl. auto.
  - exists [:: (p, u')]; repeat split; simpl.
    inversion H0; subst. dependent destruction H7.
    econstructor. rewrite -> H5. apply observe_equ_eq.
    assumption. assumption.
    unfold transAllPrb, foldr. simpl.
    rewrite addr0. rewrite le_refl. auto.
  - exists (map (enumk μ k) s); repeat split; simpl.
    apply H1. rewrite <- map_comp. exact H2.
    apply (le_trans H3). unfold transAllPrb, unzip1.
    rewrite <- map_comp. unfold ssrfun.comp, fst, mass. simpl.
    rewrite le_refl. reflexivity.
Qed.

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



#[global]
Instance pssim_equ_equ {E F : Type → Type}
    {X Y : Type} (L : rel (@label E) (@label F))
  : Proper (equ (R1 := X) eq ==> equ (R1 := Y) eq ==> flip impl)
    (pssim L).
Proof. Admitted.



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

Notation "[ R ; l ; p | ?→  t ∥ u  →→]" := (pssim_cond R t l p u).

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
Proof. unfold Reflexive.
  intros t l p t' Htrans. inversion Htrans; subst.
  - exists (val r); split; auto. inversion Htrans.
    econstructor. rewrite H4. apply Htrans. auto.
  - exists tau; split; auto. econstructor.
    rewrite H1. apply Htrans. auto.
  - exists (obs e x); split; auto. econstructor.
    rewrite H1. apply Htrans. auto.
  - exists tau; split; auto. econstructor.
    apply subseq_refl. apply transAll_Prob.
    admit. unfold disc_mass. simpl. exact le_acc_mass_mass_supp.
Admitted.



Ltac __use_pssim Hpssim Htrans :=
  idtac "use pssim";
  apply Hpssim in Htrans;
  let l := fresh "l'" in
  let RL := fresh "RL" in
  let Hpssim_cond := fresh "Hpssim_cond" in
  destruct Htrans as [l [RL Hpssim_cond]].

#[global]
Instance Transitive_pss {RC : relation (ptree E X)}
    `{Transitive _ L} `{Transitive _ RC}
  : Transitive (pss L RC).
Proof. unfold Transitive.
  intros s t u Hst Htu. intros l p t' Htrans.
  __use_pssim Hst Htrans. inversion Hpssim_cond; subst.
  - inversion H2; subst. rewrite <- H1 in Hpssim_cond.
    exists (val r); split; auto.
    rewrite <- H1 in Htu.


Admitted.

#[global]
Instance Reflexive_hpssim `{Reflexive _ L} (RC : Chain (@pss E E X X L))
  : Reflexive (` RC).
Proof. revert RC. apply Reflexive_chain.
  intros RC HRC x. apply Reflexive_pss.
Qed.

#[global]
Instance Transitive_hpssim `{Transitive _ L} (RC : Chain (@pss E E X X L))
  : Transitive (` RC).
Proof. revert RC. apply Transitive_chain.
  intros RC HRC x. apply Transitive_pss.
Qed.

End homogenous_pssim_theory.
