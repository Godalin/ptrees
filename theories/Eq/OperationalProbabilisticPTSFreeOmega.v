Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.
From PTree.Eq Require Import ShallowNew UnifiedFrontier
  OperationalProbabilisticPTS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FreeOmegaOperationalCofinality.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmegaInterface MN NI}.

Local Notation MF := (FreeOmega MN).

(** A concrete, finite obligation replacing the abstract Bind lub equality:
    every global-fuel approximant is contained in some diagonal approximant,
    and conversely. *)
Definition free_operational_bind_approx_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) : Prop :=
  free_omega_chains_cofinal eq
    (fun fuel => operational_hitting_approx (MF := MF) fuel
      (observe (PTree.bind t k)))
    (fun fuel => operational_bind_diagonal_approx (MF := MF) fuel t k).

Theorem free_operational_bind_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  free_operational_bind_approx_cofinal t k ->
  @operational_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A R t k.
Proof.
  intros Hcofinal out. unfold operational_bind_cofinal.
  apply free_omega_cofinal_lub_iff. exact Hcofinal.
Qed.

Lemma free_operational_bind_ret_approx_cofinal {A R}
    (a : A) (k : A -> ptree E MN R) :
  free_operational_bind_approx_cofinal (Ret a) k.
Proof.
  split; intro n; exists n;
    unfold free_operational_bind_approx_cofinal,
      operational_bind_diagonal_approx,
      operational_head_bind_approx,
      operational_hitting_approx, operational_kernel;
    cbn.
  all: rewrite observe_bind; cbn.
  all: rewrite operational_target_stableE; cbn.
  all: apply free_omega_approx_refl; intros x; reflexivity.
Qed.

Corollary free_operational_bind_ret_cofinal {A R}
    (a : A) (k : A -> ptree E MN R) :
  @operational_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A R (Ret a) k.
Proof.
  apply free_operational_bind_cofinal.
  apply free_operational_bind_ret_approx_cofinal.
Qed.

(** The analogous finite obligation for iteration rounds.  This is where
    bounded cost/productivity proofs for concrete samplers belong. *)
Definition free_operational_iter_approx_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) : Prop :=
  free_omega_chains_cofinal eq
    (fun fuel => operational_hitting_approx (MF := MF) fuel
      (observe (PTree.iter step i)))
    (fun rounds => operational_iter_round_approx (MF := MF)
      rounds transition i).

Theorem free_operational_iter_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) :
  free_operational_iter_approx_cofinal step transition i ->
  @operational_iter_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface I R step transition i.
Proof.
  intros Hcofinal out. unfold operational_iter_cofinal.
  apply free_omega_cofinal_lub_iff. exact Hcofinal.
Qed.

End FreeOmegaOperationalCofinality.
