(** Transition Relation of the Probabilistic Trees

    This file contains the theory of *Probabilistic
    Bisimulation* of [ptree]s.
 *)

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
From mathcomp Require Import eqtype ssralg.

From PTree.Core Require Import PTreeDefinitionNew Utils.
From PTree.Prob Require Import RatSubTypes DiscreteMC.
From PTree.Eq Require Import EquNew ShallowNew.



#[local] Ltac inv H := inversion H; clear H; subst.
#[local] Tactic Notation "step" := __step_equ.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_equ H.

(* To use the relation algebra library,
  the universe check should be unset. *)
#[local] Unset Universe Checking.

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



Import NonnegQNotations.
Import GRing.Theory.

Inductive trans_ : label → ℚ≥0 → hrel S' S' :=
  | StepTau t u
    : t ≅ u ->
      trans_ tau 1 (TauF t) (observe u)
  | StepObs {X} (e : E X) k x t
    : k x ≅ t ->
      trans_ (obs e x) 1 (VisF e k) (observe t)
  | StepVal r μ k
    : trans_ (val r) 1 (RetF r) (ProbF0 μ k)
  | StepPrb {X : eqType} (μ : M X) k x p t
    : disc_mass x μ = p ->
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
  - intros. FtoObs. constructor. rewrite H0.
    rewrite (ptree_eta u). symmetry. step. auto.
  - intros. FtoObs. constructor. rewrite H0.
    rewrite (ptree_eta t). symmetry. step. auto.
  - intros. dependent destruction EQU.
    econstructor.
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
    constructor. symmetry. transitivity t.
    symmetry. all: auto.
  - intros. dependent destruction Heqt.
    constructor. symmetry. rewrite <- H0.
    apply REL.
  - intros. dependent destruction Heqt.
    constructor.
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


(* Section test. *)
(* Import Enum. *)
(* Context {E : Type → Type}. *)
(* Context {R : Type}. *)
(* Variable u t : ptree E Enum R. *)
(* Variable l : @label E. *)

(* Check trans l 1%R u t. *)
(* Check trans. *)

Module Import TransNotations.
Infix "---[ l ; p ]-->" := (trans l p) (at level 70).
End TransNotations.
