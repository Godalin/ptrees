Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Arith.PeanoNat.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.
From PTree.Eq Require Import
  FiniteInternal PrimitiveStableHitting PTreeKernel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FreeOmegaFiniteInternal.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmega MN NI} {R : Type}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation execute :=
  (@finite_internal E MN MF FI FreeOmegaMixedMeasure R).
Local Notation hit := (@ptree_hitting_approx E MN MF FI
  FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega R).

(** A compression cannot hide an observation already reached in n primitive
    steps.  The right-hand side may reveal more behavior, since those n
    steps start only after the well-founded compression.  The index is used
    for the soundness proof, not as a bound on [finite_internal]. *)
Theorem finite_internal_hitting_covered t out :
  execute t out -> forall n,
  free_omega_approx eq (hit n (observe t))
    (free_omega_bind out (fun u => hit n (observe u))).
Proof.
  intro Hexec. induction Hexec; intro n.
  - cbn. apply free_omega_approx_refl. intro h. reflexivity.
  - destruct n as [|n].
    + apply FOApproxZero.
    + change (free_omega_approx eq (hit n (observe t))
        (free_omega_bind out (fun u => hit (S n) (observe u)))).
      eapply free_omega_approx_trans; [|apply IHHexec].
      exact (@PTreeKernel.ptree_hitting_mono E MN MF FI
        FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
        FreeOmegaObservableSemanticMeasureOrderLaws R (observe t)
        n (S n) (Nat.le_succ_diag_r n)).
  - destruct n as [|n].
    + change (free_omega_approx eq (FOSample mu (fun _ => FOZero))
        (FOSample mu (fun x => free_omega_bind (out x)
          (fun u => hit 0 (observe u))))).
      eapply FOApproxSample with (S := eq).
      * apply sem_lift_refl. intro x. reflexivity.
      * intros x y ->. apply FOApproxZero.
    + change (free_omega_approx eq (FOSample mu (fun x => hit n (observe (k x))))
        (FOSample mu (fun x => free_omega_bind (out x)
          (fun u => hit (S n) (observe u))))).
      eapply FOApproxSample with (S := eq).
      * apply sem_lift_refl. intro x. reflexivity.
      * intros x y ->. eapply free_omega_approx_trans; [|apply H0].
        exact (@PTreeKernel.ptree_hitting_mono E MN MF FI
          FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
          FreeOmegaObservableSemanticMeasureOrderLaws R (observe (k y))
          n (S n) (Nat.le_succ_diag_r n)).
Qed.

End FreeOmegaFiniteInternal.
