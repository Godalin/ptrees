(** Transition Relation of the Probabilistic Trees

    This file contains the theory of *Probabilistic
    Bisimulation* of [ptree]s.
 *)

Set Warnings "-notation-incompatible-prefix".
Set Warnings "-ambiguous-paths".

Require Import Utf8.
Require Import Program Morphisms.

From Coinduction Require Import all.
From RelationAlgebra Require Import
     monoid
     kat
     kat_tac
     prop
     rel
     srel
     comparisons
     rewriting
     normalisation.
From mathcomp Require Import ssreflect ssrbool eqtype seq finset ssralg order.

From PTree.Core Require Import PTreeDefinitionNew Utils.
From PTree.Prob Require Import RatSubTypes DiscreteMC.
From PTree.Eq Require Import EquNew ShallowNew.



#[local] Ltac inv H := inversion H; clear H; subst.
#[local] Tactic Notation "step" := __step_equ.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_equ H.

(* To use the relation algebra library,
  the universe check should be unset. *)
Unset Universe Checking.

Section Trans.
Import PTree.
Import EquNotations.
#[local] Open Scope ptree_scope.

Context {E : Type → Type}.
Context {M : Type → Type}.
Context `{DiscreteInterface M}.
Context {R : Type}.

#[local] Notation S' := (ptree' E M R).
#[local] Notation S := (ptree E M R).



Definition SS : EqType :=
  {| type_of := S; Eq := equ eq |}.

(** Labels of the LTS.
    (* TODO *) [prb] can contain "density" in continuous cases. *)

Inductive label : Type :=
  | tau
  | obs {X : Type} (e : E X) (v : X)
  | val {X : Type} (v : X).

Variant is_val : label → Prop :=
  | Is_val : forall X (x : X), is_val (val x).

Lemma is_val_tau : ¬ is_val tau.
Proof. intros Contra. inversion Contra. Qed.

Lemma is_val_obs {X} (e : E X) x : ¬ is_val (obs e x).
Proof. intros Contra. inversion Contra. Qed.



Import Enum.
Import NonnegQNotations.
Import GRing.Theory.


Inductive trans_ : label → ℚ≥0 → hrel S' S' :=
  | StepVal r μ k
    : trans_ (val r) 1 (RetF r) (ProbF0 μ k)
  | StepTau t u
    : t ≅ u ->
      trans_ tau 1 (TauF t) (observe u)
  | StepObs {X} (e : E X) k x t
    : k x ≅ t ->
      trans_ (obs e x) 1 (VisF e k) (observe t)
  | StepPrb {X : eqType} (μ : M X) k x p t
    : disc_mass x μ = p ->
      (* x \in disc_supp μ -> *)
      k x ≅ t ->
      trans_ tau p (ProbF μ k) (observe t).
Hint Constructors trans_ : core.

Definition transR l p : hrel S S
  := fun u v => trans_ l p (observe u) (observe v).

Ltac FtoObs :=
  match goal with
  | |- trans_ _ _ _ ?t =>
    change t with (observe {| _observe := t |})
  end.



#[local] Instance trans_equ_aux1 l p t
  : Proper (going (equ eq) ==> flip impl) (trans_ l p t).
Proof. intros u u' Heq. intros TR.
  inv Heq. rename H0 into EQU.
  step in EQU. revert u EQU.
  dependent induction TR.
  - intros. dependent destruction EQU.
    econstructor.
  - intros. FtoObs. constructor. rewrite H0.
    rewrite (ptree_eta u). symmetry. step. auto.
  - intros. FtoObs. constructor. rewrite H0.
    rewrite (ptree_eta t). symmetry. step. auto.
  - intros. FtoObs. econstructor; eauto.
    rewrite H1. rewrite (ptree_eta t). symmetry. step. auto.
Qed.

#[local] Instance trans_equ_aux2 l p
  : Proper (going (equ eq) ==> going (equ eq) ==> impl) (trans_ l p).
Proof. intros t1 t2 Heqt u1 u2 Hequ TR.
  rewrite <- Hequ. clear u2 Hequ.
  inv Heqt. rename H0 into Heqt. step in Heqt.
  revert t2 Heqt. dependent induction TR.
  - intros. dependent destruction Heqt.
    constructor.
  - intros. dependent destruction Heqt.
    constructor. symmetry. transitivity t.
    symmetry. all: auto.
  - intros. dependent destruction Heqt.
    constructor. symmetry. rewrite <- H0.
    apply REL.
  - intros. dependent destruction Heqt.
    econstructor.
    rewrite <- REL. eassumption.
    symmetry. rewrite <- H1. apply RELk.
Qed.

#[global] Instance trans_equ_ l p
  : Proper (going (equ eq) ==> going (equ eq) ==> iff) (trans_ l p).
Proof. intros ?? EQt ?? EQu. split; intro TR.
  - eapply trans_equ_aux2; eauto.
  - symmetry in EQt. symmetry in EQu.
    eapply trans_equ_aux2; eauto.
Qed.

#[global] Instance trans_equ l p
  : Proper (equ eq ==> equ eq ==> iff) (transR l p).
Proof. intros ?? EQt ?? EQu. unfold transR.
  rewrite EQt. rewrite EQu. reflexivity.
Qed.

Definition trans l p : srel SS SS :=
  {| hrel_of := transR l p : hrel SS SS |}.

Lemma trans__trans : forall l p t u,
  trans_ l p (observe t) (observe u) = trans l p t u.
Proof. reflexivity. Qed.

Lemma transR_trans : forall l p t u,
  transR l p t u = trans l p t u.
Proof. reflexivity. Qed.



Definition etrans l p : srel SS SS :=
  match l with
  | tau => (cup (trans l p) 1)
  | _ => trans l p
  end.

Definition wtrans l : srel SS SS :=
  (trans tau 1)^* ⋅ etrans l 1 ⋅ (trans tau 1)^*.

Definition pwtrans l : srel SS SS :=
  (trans tau 1)^* ⋅ trans l 1 ⋅ (trans tau 1)^*.

Definition tautrans : srel SS SS :=
  (trans tau 1)^+.

End Trans.

Section Trans_relation.

Import Enum.
Import NonnegQNotations.

Fixpoint transAll {E} {R} α (t : ptree E Enum R)
    (tlist : Enum (ptree E Enum R)) : Prop :=
  match tlist with
  | [::] => True
  | (p, t') :: tlist' => trans α p t t' ∧ transAll α t tlist'
  end.

Definition transAllPrb {E X} (tlist : Enum (ptree E Enum X)) : ℚ≥0 :=
  sumq (unzip1 tlist).

Fixpoint relateAll {X Y} (R : rel X Y) (x : X) (ys : list Y) : Prop :=
  match ys with
  | [::] => True
  | y :: ys' => R x y ∧ relateAll R x ys'
  end.

Lemma relateAll_sub {X Y} (R S : rel X Y) (x : X) (ys : list Y)
  : (∀ x y, R x y → S x y) → relateAll R x ys → relateAll S x ys.
Proof. elim: ys => [//|y ys IH //= H] [Hxy Hxys]. auto. Qed.

Lemma relateAll_trans {X} (R : relation X) `{Transitive _ R}
  : ∀ (x y : X) (zs : list X), R x y → relateAll R y zs → relateAll R x zs.
Proof. intros. induction zs.
  auto. simpl in H1. destruct H1 as [Rya RAyzs].
  simpl. split. etransitivity; eauto.
  apply IHzs. eauto.
Qed.

Lemma transAll_Prob_Cons {E} {X : eqType} {Y} {k : X -> ptree E Enum Y} (x : Enum X) (p : ℚ≥0 * X) (l : seq X)
  : transAll tau (Prob x k) [seq enumk x k x0  | x0 <- l] -> transAll tau (Prob (p :: x) k) [seq enumk (p :: x) k x0 | x0 <- l].
Proof.
  move => ih. induction l. rewrite //=.
  rewrite map_cons /transAll in ih. destruct ih.
  have ih1 := IHl H0. clear IHl H0.
  rewrite map_cons /transAll. split.
  econstructor. reflexivity. reflexivity. exact ih1.
Qed.

Lemma transAll_Prob {E} {X : eqType} {Y}
  : forall (μ : Enum X) (k : X -> ptree E Enum Y), transAll tau (Prob μ k) [seq enumk μ k x | x <- supp μ].
Proof.
  move => μ k. elim : μ => [//|p x ih]. rewrite /supp /unzip2 map_cons /undup -/undup.
  case: (snd p \in [seq snd i | i <- x]).
  (* p in [seq snd i  | i <- x] *)
  rewrite /enumk. eapply transAll_Prob_Cons. exact: ih.

  (* p not in [seq snd i  | i <- x] *)
  rewrite /enumk map_cons /transAll. split.
  econstructor. reflexivity. reflexivity.
  eapply transAll_Prob_Cons. exact: ih.
Qed.
End Trans_relation.


Module Import TransNotations.
Infix "---[ l ; p ]-->" := (trans l p) (at level 70).
End TransNotations.
