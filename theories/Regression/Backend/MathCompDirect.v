(** Gate M only. Never imported by the safe AllImports aggregate.
    Direct capability and program acceptance; not a universe-consistency claim.
    The checked negative counterparts remain in MathCompUniverse.v. *)
Set Warnings "-ambiguous-paths".
Local Unset Universe Checking.
Require PTree.Regression.Backend.FreeOmegaUpperContracts.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order reals boolp
  classical_sets measure ereal.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure NativeLaws OrderLaws OmegaLaws BindLaws Retry.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel PEutt.
From PTree.Eq.Backend.MathComp Require Import Direct.
From PTree.Examples Require Import MathCompPrograms.
From PTree.API Require Import Behavior.
Set Implicit Arguments.
Import GRing.Theory Num.Theory Order.Theory.

Section Probes.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation MX := (MathCompNativeMixedMeasure R).
Local Notation E := (fun _ : Type => Empty_set).

Definition direct_ret : ptree E M bool := Ret true.
Definition direct_frontier : Type := @mathcomp_direct_frontier R E bool.
Definition direct_kernel := @mathcomp_direct_kernel R E bool.
Definition direct_hitting := @mathcomp_direct_hitting R E bool.

(** Positive assembly probes consume the checked native instances. *)
Definition available_native_order : @SemanticMeasureOrderLaws M NI NO := _.
Definition available_native_omega : @SemanticOmegaLaws M NI NO := _.
Definition available_general_hitting_exists :=
  @ptree_stable_hitting_exists E M M NI MX NO _ _ bool.

Context `{G : MathCompCouplingGluing R}.
Example direct_canonical_profile {F A B} (RR : A -> B -> Prop)
    (t : ptree F M A) (u : ptree F M B) :
  canonical_peutt RR t u =
  @peutt F M M NI (@MathCompNodeSemanticMeasureCoreLaws R G)
    MX NO A B RR t u.
Proof. reflexivity. Qed.

Example direct_ret_reflexivity :
  @mathcomp_direct_peutt R G E bool direct_ret direct_ret.
Proof. apply mathcomp_direct_peutt_refl. Qed.

Example direct_eventful_reflexivity {F A} (t : ptree F M A) :
  @mathcomp_direct_peutt R G F A t t.
Proof. apply mathcomp_direct_peutt_refl. Qed.
End Probes.

Section Programs.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation MX := (MathCompNativeMixedMeasure R).
Context {E : Type -> Type} {A : Type}.
Variable q : R.
Hypothesis Hq : (0 < q <= 1)%R.
Variable value : A.
Local Notation retry := (@mathcomp_retry E A R (mathcomp_bernoulli q) value).
Local Notation hits := (@mathcomp_direct_hitting R E A).
Local Notation W := (@mathcomp_direct_peutt R G E A).

Lemma direct_retry_hitting : hits (observe retry) (sem_ret (FHRet value)).
Proof.
  destruct (mathcomp_direct_hitting_exists R retry) as [out Hout].
  assert (Htau : hits (observe (Tau retry)) out).
  { apply (proj2 (ptree_stable_hitting_tau_iff _ _)); exact Hout. }
  assert (Hprob : hits (observe retry)
    (sem_bind (mathcomp_bernoulli q)
      (fun b => if b then sem_ret (FHRet value) else out))).
  { rewrite mathcomp_retry_observe.
    eapply (ptree_stable_hitting_prob (MX := MX)) with (Good := fun _ => True).
    - apply mathcomp_kernel_ae_true.
    - intros [] _; [apply ptree_stable_hitting_ret|exact Htau]. }
  assert (He : mathcomp_kernel_eq out (sem_ret (FHRet value))).
  { apply (@mathcomp_retry_fixed_point R _ q out (sem_ret (FHRet value)) Hq).
    exact (ptree_stable_hitting_unique Hout Hprob). }
  exact (mathcomp_kernel_lub_limit_proper He Hout).
Qed.

Example direct_unbounded_retry : W retry (Ret value).
Proof.
  eapply peutt_of_hitting_lift.
  - exact direct_retry_hitting.
  - apply stable_hitting_ret.
  - apply mathcomp_kernel_lift_ret. constructor; reflexivity.
Qed.

Example direct_retry_before_vis {X} (e : E X)
    (k : X -> ptree E M A) :
  W (Vis e (fun x => Tau (k x))) (Vis e k).
Proof. apply peutt_vis; intros x; apply peutt_tau_l. Qed.

End Programs.

Section Composition.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation MX := (MathCompNativeMixedMeasure R).
Context {E : Type -> Type} {A : Type}.
Variables q p : R.
Hypotheses (Hq : (0 < q <= 1)%R) (Hp : (0 < p <= 1)%R).
Variable value : A.
Local Notation outer := (@mathcomp_retry E unit R (mathcomp_bernoulli q) tt).
Local Notation inner := (@mathcomp_retry E A R (mathcomp_bernoulli p) value).
Local Notation W := (@mathcomp_direct_peutt R G E A).

Example direct_eventful_bind_rewrite (k : unit -> ptree E M A) :
  W (PTree.bind outer k) (k tt).
Proof.
  change (W (PTree.bind outer k) (PTree.bind (Ret tt) k)).
  eapply mathcomp_direct_peutt_bind with (RR := eq).
  - apply direct_unbounded_retry; exact Hq.
  - intros x y ->; apply mathcomp_direct_peutt_refl.
Qed.

Example direct_nested_unbounded_retry :
  W (PTree.bind outer (fun _ => inner)) (Ret value).
Proof.
  eapply peutt_trans.
  - apply direct_eventful_bind_rewrite.
  - apply direct_unbounded_retry; exact Hp.
Qed.

(** Both approximation indices describe genuinely unbounded retries. This
    is the diagonal/Fubini route, not a finite maximum of inner stopping times. *)
Example direct_nested_retry_diagonal :
  @sem_lub M NI NO _
    (fun n => @ptree_bind_diagonal_approx E M M NI MX NO unit A n
      outer (fun _ => inner)) (sem_ret (FHRet value)).
Proof.
  pose front (_ : unit) : M (stable_head E M A) :=
    @sem_ret M NI _ (FHRet value).
  pose next := @stable_head_bind_front E M M NI unit A (fun _ => inner) front.
  apply (@mathcomp_kernel_lub_limit_proper R _ _
    (mathcomp_kernel_bind (sem_ret (FHRet tt)) next)).
  - apply mathcomp_kernel_bind_ret_l.
  - unfold ptree_bind_diagonal_approx.
    apply (sem_bind_diagonal_lub (S := M) (SI := NI) (SO := NO)).
    + apply ptree_hitting_increasing.
    + intro head; apply ptree_head_bind_approx_increasing.
    + exact (@direct_retry_hitting R G E unit q Hq tt).
    + intro head; apply ptree_head_bind_approx_lub.
      intro x; exact (@direct_retry_hitting R G E A p Hp value).
Qed.

Example direct_retry_vis_interaction {X} (e : E X)
    (k : X -> ptree E M A) :
  W (PTree.bind outer (fun _ => Vis e k)) (Vis e k).
Proof. apply direct_eventful_bind_rewrite. Qed.
End Composition.
