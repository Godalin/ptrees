(** Opt-in, backend-parametric stable-frontier syntax. Technical checks
    belong here, outside the installed theory and mathematical examples. *)
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel.

Import HittingNotations FrontierCertificateNotations.
Import SemanticMeasureNotations SemanticOmegaNotations.
Fail Check (Ret tt ⇓ₕ sem_ret (FHRet tt)).
Fail Check stable_head_bind_front.

Section Generic.
Context {E MN MF : Type -> Type}
  {NI : SemanticMeasure MN} {FI : SemanticMeasure MF}
  {MX : MixedMeasure MN MF} {FO : @SemanticOmega MF FI}.
Context {A : Type} (t : ptree E MN A) (front : MF (stable_head E MN A)).

Example delimited_hitting :
  (t ⇓ₕ front)%hit = @ptree_stable_hitting E MN MF FI MX FO A (observe t) front.
Proof. reflexivity. Qed.

Local Open Scope hitting_scope.
Local Open Scope semantic_measure_scope.

Example hitting_expansion :
  (t ⇓ₕ front) = stable_hitting (@ptree_primitive_kernel E MN MF FI MX A)
    (observe t) front.
Proof. reflexivity. Qed.
Example total_frontier_expansion :
  (t ⇓ₕ¹ front) = (t ⇓ₕ front /\ sem_total front).
Proof. reflexivity. Qed.
Example approximant_expansion n :
  hit[n] t = @ptree_hitting_approx E MN MF FI MX FO A n (observe t).
Proof. reflexivity. Qed.
Example hitting_is_the_lub :
  (t ⇓ₕ front) = ((fun n => hit[n] t) ⇑ₘ front).
Proof. reflexivity. Qed.
Example certificate_expansion :
  (t ⊢F front) = @frontier_certificate E MN MF NI FI MX FO A (observe t) front.
Proof. reflexivity. Qed.
Fail Definition certificate_is_semantics : (t ⊢F front) = (t ⇓ₕ front) := eq_refl.
Fail Definition complete_means_total : (t ⇓ₕ front) = (t ⇓ₕ¹ front) := eq_refl.
Example conjunction_parsing :
  (t ⊢F front /\ t ⇓ₕ front) =
  (frontier_certificate (observe t) front /\ ptree_stable_hitting (observe t) front).
Proof. reflexivity. Qed.
Example finite_formula_parsing n :
  (hit[n] t ≤ₘ hit[S n] t) =
  sem_le (ptree_hitting_approx n (observe t)) (ptree_hitting_approx (S n) (observe t)).
Proof. reflexivity. Qed.
End Generic.

Fail Check (Ret tt ⇓ₕ sem_ret (FHRet tt)).

(** Observable FreeOmega, even after explicitly loading structural laws.
    The notation has no competing structural interpretation of its own. *)
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Measure StructuralMeasure.
Local Open Scope hitting_scope.
Local Open Scope freeomega_scope.
Section Observable.
Context {E MN : Type -> Type} {NI : SemanticMeasure MN}
  {NO : @SemanticOmega MN NI} {A : Type} (t : ptree E MN A).
Variable front : FreeOmega MN (stable_head E MN A).
Example observable_profile :
  (t ⇓ₕ front) = @ptree_stable_hitting E MN (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)) A (observe t) front.
Proof. reflexivity. Qed.
Example zero_fuel : hit[0] (Tau t) = (⊥ω : FreeOmega MN (stable_head E MN A)).
Proof. reflexivity. Qed.
End Observable.
