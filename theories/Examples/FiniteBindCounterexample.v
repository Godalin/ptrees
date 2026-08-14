Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg rat.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC Coupling IndexedCoupling
  FrontierLift FrontierLiftEnum.
From PTree.Eq Require Import ShallowNew PWeakAbstract.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum Coupling IndexedCoupling.
Import GRing.Theory.

Unset Automatic Proposition Inductives.
Variant finite_bindE : Type -> Type := .

Definition finite_bind_singleton : Enum unit := ret_Enum tt.

CoFixpoint finite_weak_spin {R} : ptree finite_bindE Enum R :=
  Tau finite_weak_spin.

Lemma observe_finite_weak_spin {R} :
  observe (@finite_weak_spin R) = TauF finite_weak_spin.
Proof. reflexivity. Qed.

Definition finite_dirac_return : ptree finite_bindE Enum unit :=
  Prob finite_bind_singleton (fun _ => Ret tt).

Definition finite_dirac_heads : Enum (aphead finite_bindE Enum unit) :=
  meas_bind finite_bind_singleton (fun _ =>
    meas_ret (APHRet tt : aphead finite_bindE Enum unit)).

Lemma finite_dirac_return_frontier :
  apfrontier (observe finite_dirac_return) finite_dirac_heads.
Proof.
  unfold finite_dirac_return, finite_dirac_heads.
  eapply APFProb with (Good := fun _ => True).
  - apply meas_ae_true.
  - intros [] _. constructor.
Qed.

Lemma finite_dirac_return_equivalent_to_return :
  apweak eq finite_dirac_return (Ret tt).
Proof.
  apply apweak_fold.
  eapply APWFrontier with
      (hs1 := finite_dirac_heads)
      (hs2 := meas_ret (APHRet tt : aphead finite_bindE Enum unit)).
  - exact finite_dirac_return_frontier.
  - constructor.
  - change (indexed_coupling
      (aphead_rel eq (@apweak finite_bindE Enum
        Enum_MeasureInterface Enum_MeasureCoreLaws unit unit eq))
      (enum_prune finite_dirac_heads)
      (enum_prune (ret_Enum
        (APHRet tt : aphead finite_bindE Enum unit)))).
    rewrite /finite_dirac_heads /finite_bind_singleton
      /bind_Enum /ret_Enum /= mulr1.
    apply indexed_coupling_refl.
    apply aphead_rel_refl. apply apweak_refl.
Qed.

Lemma finite_weak_spin_has_no_frontier {R} hs :
  ~ apfrontier (TauF (@finite_weak_spin R)) hs.
Proof.
  intros Hf.
  remember (TauF (@finite_weak_spin R)) as ot eqn:Hot in Hf.
  induction Hf; try discriminate.
  apply IHHf. inversion Hot; subst t.
  exact observe_finite_weak_spin.
Qed.

Lemma apweakF_prob_finite_spin_absurd
    (sim : ptree finite_bindE Enum unit ->
      ptree finite_bindE Enum unit -> Prop)
    (k : unit -> ptree finite_bindE Enum unit) :
  apweakF eq sim
    (ProbF finite_bind_singleton k)
    (TauF (@finite_weak_spin unit)) -> False.
Proof.
  intros Hstep.
  remember (ProbF finite_bind_singleton k) as lhs eqn:Hlhs in Hstep.
  remember (TauF (@finite_weak_spin unit)) as rhs eqn:Hrhs in Hstep.
  induction Hstep; try discriminate.
  - rewrite Hrhs in H0. exact (finite_weak_spin_has_no_frontier H0).
  - apply IHHstep.
    + exact Hlhs.
    + inversion Hrhs; subst t2. exact observe_finite_weak_spin.
Qed.

Definition finite_bind_to_spin (_ : unit) :
    ptree finite_bindE Enum unit := finite_weak_spin.

(** Finite-frontier equivalence forgets a terminating Dirac node.  Binding
    both sides to pure divergence exposes that node again, so unrestricted
    bind is not a congruence for [apweak].  This theorem deliberately makes
    no stronger claim about the AST-aware unified relation. *)
Theorem finite_unrestricted_bind_congruence_fails :
  ~ apweak eq
      (PTree.bind finite_dirac_return finite_bind_to_spin)
      (PTree.bind (Ret tt) finite_bind_to_spin).
Proof.
  intros Hrel. apply apweak_unfold in Hrel.
  rewrite !observe_bind in Hrel. cbn in Hrel.
  exact (apweakF_prob_finite_spin_absurd Hrel).
Qed.
