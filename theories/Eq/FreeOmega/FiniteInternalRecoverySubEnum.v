Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum
  FreeOmegaMeasure FreeOmegaNative FreeOmegaRecoverySubEnum.
From PTree.Eq Require Import FiniteInternalPlan PFinite.
From PTree.Eq.FreeOmega Require Import FiniteInternalNative FiniteInternalRoundCoupling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** For SubEnum, every well-founded compression admits distribution-
    preserving path recovery.  This removes the decoder-injectivity and
    per-plan recovery obligations, but does NOT yet realize a joint round
    or prove unrestricted residual-GFP soundness. *)
Section Paths.
Context {E : Type -> Type} {A B : Type}.
Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Variable RR : A -> B -> Prop.
Variable sim : ptree E SubEnum A -> ptree E SubEnum B -> Prop.

Theorem pfinite_subenum_path_characterization t u :
  @pfiniteF E SubEnum MF SubEnum_SemanticMeasure FI
    FreeOmegaMixedMeasure A B RR sim t u <->
  exists (p : @finite_internal_plan E SubEnum A t)
         (q : @finite_internal_plan E SubEnum B u),
    free_omega_qlift
      (fun x y => pfinite_guard RR sim
        (internal_plan_residual p x) (internal_plan_residual q y))
      (FOSample (internal_plan_measure p) (fun x => FORet x) :
        FreeOmegaAt SubEnum (ptree E SubEnum A) (internal_plan_path p))
      (FOSample (internal_plan_measure q) (fun y => FORet y) :
        FreeOmegaAt SubEnum (ptree E SubEnum B) (internal_plan_path q)).
Proof.
  rewrite pfinite_native_characterization.
  split; intros [p [q H]]; exists p, q.
  - exact (subenum_native_coupling_pullback
      (p := internal_plan_native p) (q := internal_plan_native q) H).
  - change (free_omega_qlift (pfinite_guard RR sim)
      (free_omega_bind (FOSample (internal_plan_measure p) (fun x => FORet x))
        (fun x => FORet (internal_plan_residual p x)))
      (free_omega_bind (FOSample (internal_plan_measure q) (fun y => FORet y))
        (fun y => FORet (internal_plan_residual q y)))).
    eapply FOQLBind; [exact H|].
    intros x y Hxy. apply FOQLStructural, FOLRet. exact Hxy.
Qed.

(** The recovered compression path can now execute its matched guard.
    Each sample retains BOTH pieces of its path, hence its actual cost is
    still available to costed projection.  This is not yet a joint row. *)
Theorem pfinite_subenum_round_paths t u :
  @pfiniteF E SubEnum MF SubEnum_SemanticMeasure FI
    FreeOmegaMixedMeasure A B RR sim t u ->
  exists (p : @finite_internal_plan E SubEnum A t)
         (q : @finite_internal_plan E SubEnum B u),
    free_omega_qlift (internal_round_path_rel RR sim p q)
      (FOSample (native_sample_measure (internal_plan_round_native p)) (fun x => FORet x))
      (FOSample (native_sample_measure (internal_plan_round_native q)) (fun y => FORet y)).
Proof.
  intro H. apply pfinite_subenum_path_characterization in H.
  destruct H as [p [q Hpaths]]. exists p, q.
  apply internal_plan_round_paths_coupled. exact Hpaths.
Qed.
End Paths.
