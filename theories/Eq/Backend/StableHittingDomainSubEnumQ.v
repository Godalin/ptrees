(** Role: Rational specialization and compatibility names for generic PTree
    stable-hitting validation. The independent kernel and finite/limit proof
    now belong to Validation/StableHitting; this file does not re-prove them.
    New clients use modelable/model_denotes; admissible/domain names remain
    compatibility endpoints for existing rational clients. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Domain Require Import Expectation.
From PTree.Prob.Interface Require Import Measure Omega.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import StructuralMeasure Measure.
From PTree.Prob.Backend.SubEnumQ Require Import Measure Domain Expectation.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import Compatibility Validation.
From PTree.Prob.FreeOmega.Validation Require Import Model StableHitting.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier PTreeKernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

(** Mathematical hitting for any OmegaVal kernel. No FreeOmega evaluator
    or syntactic approximation occurs in these definitions or proofs. *)
Section DomainKernel.
Variable R : realType.
Context {S H : Type}.
Variable K : S -> OmegaVal R (stable_target S H).

Definition domain_target_approx := @StableHitting.domain_target_approx R S H K.
Definition domain_hitting_approx := @StableHitting.domain_hitting_approx R S H K.

Lemma domain_target_approx_increasing n z :
  oval_le (domain_target_approx n z) (domain_target_approx (Datatypes.S n) z).
Proof.
  exact: StableHitting.domain_target_approx_increasing.
Qed.

Lemma domain_hitting_approx_increasing s : oval_increasing (fun n => domain_hitting_approx n s).
Proof.
  exact: StableHitting.domain_hitting_approx_increasing.
Qed.

Definition domain_hitting s : OmegaVal R H := oval_lub (domain_hitting_approx_increasing s).
End DomainKernel.

Local Notation FI := (@FreeOmegaObservableSemanticMeasure SubEnumQ
  SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).
Local Notation FO := (@FreeOmegaObservableSemanticOmega SubEnumQ
  SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).

Section FiniteCommutation.
Variable R : realType.
Context {S H : Type}.
Variable K : S -> FreeOmega SubEnumQ (stable_target S H).
Variable D : S -> OmegaVal R (stable_target S H).
Hypothesis HK : forall s, free_omega_domain_denotes (K s) (D s).

Theorem stable_target_denotational_commutation n z :
  free_omega_domain_denotes
    (@stable_target_approx _ FI FO S H K n z) (domain_target_approx D n z).
Proof.
  apply (StableHitting.stable_target_denotational_commutation (native := fun X => @subenumQ_domain R X)); exact HK.
Qed.

Theorem stable_hitting_finite_commutation n s :
  free_omega_domain_denotes
    (@stable_hitting_approx _ FI FO S H K n s) (domain_hitting_approx D n s).
Proof.
  apply (StableHitting.stable_hitting_finite_commutation (native := fun X => @subenumQ_domain R X)); exact HK.
Qed.
End FiniteCommutation.

Section PTreeDomain.
Variable R : realType.
Context {E : Type -> Type} {A : Type}.
Local Notation state := (ptree' E SubEnumQ A).
Local Notation head := (stable_head E SubEnumQ A).
Local Notation K := (@ptree_primitive_kernel E SubEnumQ (FreeOmega SubEnumQ)
  FI FreeOmegaMixedMeasure A).
Local Notation approx := (@ptree_hitting_approx E SubEnumQ (FreeOmega SubEnumQ)
  FI FreeOmegaMixedMeasure FO A).
Local Notation hits := (@ptree_stable_hitting E SubEnumQ (FreeOmega SubEnumQ)
  FI FreeOmegaMixedMeasure FO A).

(** Direct mathematical interpretation of one primitive observation.
    A Prob samples the native subdistribution without normalizing its mass. *)
Definition ptree_domain_kernel :=
  @StableHitting.ptree_model_kernel SubEnumQ R (fun X => @subenumQ_domain R X) E A.

Definition ptree_domain_approx := domain_hitting_approx ptree_domain_kernel.
Definition ptree_domain_hitting := domain_hitting ptree_domain_kernel.

Lemma ptree_domain_approx_ret n a f :
  oval_eval (ptree_domain_approx n (RetF a)) f = f (FHRet a).
Proof. destruct n; reflexivity. Qed.

Lemma ptree_domain_approx_vis {X} n (e : E X) k f :
  oval_eval (ptree_domain_approx n (VisF e k)) f = f (FHVis e k).
Proof. destruct n; reflexivity. Qed.

Lemma ptree_domain_approx_tau_zero t f :
  oval_eval (ptree_domain_approx O (TauF t)) f = 0.
Proof. reflexivity. Qed.

Lemma ptree_domain_approx_tau_succ n t f :
  oval_eval (ptree_domain_approx (Datatypes.S n) (TauF t)) f =
  oval_eval (ptree_domain_approx n (observe t)) f.
Proof. reflexivity. Qed.

Lemma ptree_domain_approx_prob_zero {X} (mu : SubEnumQ X) k f :
  oval_eval (ptree_domain_approx O (ProbF mu k)) f = 0.
Proof. apply enumQ_real_expect_zero. Qed.

Lemma ptree_domain_approx_prob_succ {X} n (mu : SubEnumQ X) k f :
  oval_eval (ptree_domain_approx (Datatypes.S n) (ProbF mu k)) f =
  enumQ_real_expect (fun x => oval_eval (ptree_domain_approx n (observe (k x))) f)
    (subenumQ_raw mu).
Proof. reflexivity. Qed.

Theorem ptree_kernel_denotational_commutation s :
  free_omega_domain_denotes (K s) (ptree_domain_kernel s).
Proof.
  exact (ptree_kernel_model_commutation (fun X => @subenumQ_domain R X) s).
Qed.

Theorem ptree_hitting_finite_commutation n s :
  free_omega_domain_denotes (approx n s) (ptree_domain_approx n s).
Proof.
  exact (ptree_hitting_model_commutation (fun X => @subenumQ_domain R X) n s).
Qed.

Theorem ptree_hitting_approx_admissible n s : free_omega_admissible R (approx n s).
Proof.
  exact (ptree_hitting_approx_modelable (fun X => @subenumQ_domain R X) n s).
Qed.

Theorem ptree_hitting_approx_domain_increasing s :
  free_omega_domain_increasing R (fun n => approx n s).
Proof.
  exact (ptree_hitting_approx_model_increasing (fun X => @subenumQ_domain R X) s).
Qed.

Definition ptree_canonical_hitting (s : state) := FOLub (fun n => approx n s).

Theorem ptree_canonical_hitting_spec s : hits s (ptree_canonical_hitting s).
Proof.
  exact: StableHitting.ptree_canonical_hitting_spec.
Qed.

Theorem ptree_canonical_hitting_admissible s :
  free_omega_admissible R (ptree_canonical_hitting s).
Proof.
  exact (ptree_canonical_hitting_modelable (fun X => @subenumQ_domain R X) s).
Qed.

Theorem ptree_canonical_hitting_denotes s :
  free_omega_domain_denotes (ptree_canonical_hitting s) (ptree_domain_hitting s).
Proof.
  exact (StableHitting.ptree_canonical_hitting_denotes (fun X => @subenumQ_domain R X) s).
Qed.

(** An arbitrary complete witness is not assumed valid: DS3 transports
    validity from the canonical Lub along observable quotient equality. *)
Theorem stable_hitting_admissible s out : hits s out -> free_omega_admissible R out.
Proof.
  apply (stable_hitting_modelable (native := fun X => @subenumQ_domain R X)).
  - exact (@subenumQ_native_model_ae R).
  - exact (@subenumQ_domain_ret R).
  - exact (@subenumQ_domain_zero R).
  - exact (@subenumQ_domain_bind R).
  - exact (@subenumQ_native_model_lift R).
  - exact (@subenumQ_native_model_lub R).
Qed.

Theorem stable_hitting_denotational_adequacy s out :
  hits s out -> free_omega_domain_denotes out (ptree_domain_hitting s).
Proof.
  apply (StableHitting.stable_hitting_denotational_adequacy
    (native := fun X => @subenumQ_domain R X)).
  - exact (@subenumQ_native_model_ae R).
  - exact (@subenumQ_domain_ret R).
  - exact (@subenumQ_domain_zero R).
  - exact (@subenumQ_domain_bind R).
  - exact (@subenumQ_native_model_lift R).
  - exact (@subenumQ_native_model_lub R).
Qed.

Corollary stable_hitting_domain_eq s out (Hv : free_omega_admissible R out) :
  hits s out -> oval_eq (free_omega_domain Hv) (ptree_domain_hitting s).
Proof. intros H f Hf; exact (stable_hitting_denotational_adequacy H Hf). Qed.

Corollary stable_hitting_mass_lub s out (H : hits s out) :
  oval_mass (free_omega_domain (stable_hitting_admissible H)) =
  oval_sup (fun n => oval_mass (ptree_domain_approx n s)).
Proof. exact (stable_hitting_denotational_adequacy H (oval_test_one R)). Qed.

(** Reuse a convenient complete witness; no second induction on the
    mathematical approximants is needed for elementary program laws. *)
Theorem ptree_domain_hitting_of_denotes s out (L : OmegaVal R head) :
  hits s out -> free_omega_domain_denotes out L ->
  oval_eq (ptree_domain_hitting s) L.
Proof.
  intros Hhit Hden f Hf.
  rewrite <- (stable_hitting_denotational_adequacy Hhit Hf).
  exact (Hden f Hf).
Qed.

Corollary ptree_domain_hitting_zero s :
  hits s FOZero -> oval_eq (ptree_domain_hitting s) (oval_bottom R).
Proof.
  intro H. eapply ptree_domain_hitting_of_denotes; [exact H|].
  exact: free_omega_denote_zero.
Qed.

Theorem ptree_domain_hitting_ret a :
  oval_eq (ptree_domain_hitting (RetF a)) (oval_ret R (FHRet a)).
Proof.
  eapply ptree_domain_hitting_of_denotes.
  - apply ptree_stable_hitting_ret.
  - exact: free_omega_denote_ret.
Qed.

Theorem ptree_domain_hitting_vis {X} (e : E X) k :
  oval_eq (ptree_domain_hitting (VisF e k)) (oval_ret R (FHVis e k)).
Proof.
  eapply ptree_domain_hitting_of_denotes.
  - apply ptree_stable_hitting_vis.
  - exact: free_omega_denote_ret.
Qed.

Corollary ptree_domain_hitting_vis_mass {X} (e : E X) k :
  oval_mass (ptree_domain_hitting (VisF e k)) = 1.
Proof. exact (ptree_domain_hitting_vis e k (oval_test_one R)). Qed.

Theorem ptree_domain_hitting_spin (t : ptree E SubEnumQ A) :
  observe t = TauF t ->
  oval_eq (ptree_domain_hitting (observe t)) (oval_bottom R).
Proof.
  intro H. apply ptree_domain_hitting_zero.
  apply (ptree_stable_hitting_spin_zero (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)). exact H.
Qed.

Theorem ptree_domain_hitting_prob_empty {X} (mu : SubEnumQ X) k :
  sem_ae mu (fun _ => False) ->
  oval_eq (ptree_domain_hitting (ProbF mu k)) (oval_bottom R).
Proof.
  intro H. apply ptree_domain_hitting_zero.
  apply (ptree_stable_hitting_prob_empty (NI := SubEnumQ_SemanticMeasure)
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)). exact H.
Qed.

Corollary ptree_domain_hitting_prob_zero {X} (k : X -> ptree E SubEnumQ A) :
  oval_eq (ptree_domain_hitting (ProbF (@subenumQ_zero X) k)) (oval_bottom R).
Proof.
  apply ptree_domain_hitting_prob_empty.
  intros p x Hin. contradiction.
Qed.
(** Canonical names for new clients; old names above are compatibility only. *)
Corollary subenumQ_stable_hitting_modelable s out :
  hits s out -> free_omega_modelable (fun X => @subenumQ_domain R X) out.
Proof. exact: stable_hitting_admissible. Qed.

Corollary subenumQ_stable_hitting_denotational_adequacy s out :
  hits s out -> free_omega_model_denotes (fun X => @subenumQ_domain R X) out (ptree_domain_hitting s).
Proof. exact: stable_hitting_denotational_adequacy. Qed.
End PTreeDomain.
