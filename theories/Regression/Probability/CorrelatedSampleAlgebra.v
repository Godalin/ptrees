(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From Coq.Program Require Import Equality.
From mathcomp Require Import eqtype.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure PTree.Prob.Backend.EnumQ.SemanticCoupling.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Coupling.
From PTree.Eq.Internal Require Import FiniteInternal.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier PEutt PStrong.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternalJoint FiniteInternalJointReference.
From PTree.Regression.Semantics Require Import PEuttAlgebra.
From PTree.Regression.Backend Require Import EnumQMeasureRegression SubEnumQRegression.

Set Implicit Arguments.

(** Exchange two independent samples in EVERY retry, not just in a finite
    prefix.  No positivity, AST, or bound on the number of retries is used.
    The explicit Tau observation also avoids assuming a Leibniz eta law for
    arbitrary cofixpoints when constructing the syntax-directed cuts. *)
Section ExchangeRetries.
Unset Automatic Proposition Inductives.
Variant exchangeE : Type -> Type := .
Local Notation E := exchangeE.
Variables mu nu : SubEnumQ bool.
Local Notation tree := (ptree E SubEnumQ bool).
Local Notation Pair := (tree * tree)%type.
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).

Definition exchange_left_round (next : tree) : tree :=
  Prob mu (fun x => Prob nu (fun y => if Bool.eqb x y then Tau next else Ret x)).
Definition exchange_right_round (next : tree) : tree :=
  Prob nu (fun y => Prob mu (fun x => if Bool.eqb x y then Tau next else Ret x)).
CoFixpoint exchange_retry_left : tree := Tau (exchange_left_round exchange_retry_left).
CoFixpoint exchange_retry_right : tree := Tau (exchange_right_round exchange_retry_right).

Inductive exchange_retry_pairs : tree -> tree -> Prop :=
| ExchangeLoop : exchange_retry_pairs exchange_retry_left exchange_retry_right
| ExchangeBody : exchange_retry_pairs (exchange_left_round exchange_retry_left)
    (exchange_right_round exchange_retry_right).

Definition exchange_left_cut (p : Pair) : MF tree :=
  match observe (fst p) with
  | TauF _ => FORet (fst p)
  | _ => FOSample mu (fun x => FOSample nu
      (fun y => FORet (if Bool.eqb x y then Tau exchange_retry_left else Ret x)))
  end.
Definition exchange_right_cut (p : Pair) : MF tree :=
  match observe (fst p) with
  | TauF _ => FORet (snd p)
  | _ => FOSample nu (fun y => FOSample mu
      (fun x => FORet (if Bool.eqb x y then Tau exchange_retry_right else Ret x)))
  end.

Lemma exchange_left_cut_valid t u : exchange_retry_pairs t u ->
  @finite_internal E SubEnumQ MF FI FreeOmegaMixedMeasure bool t (exchange_left_cut (t,u)).
Proof.
  intro H. destruct H.
  - exact (@FIStop E SubEnumQ MF FI FreeOmegaMixedMeasure bool exchange_retry_left).
  - apply (@FIProb E SubEnumQ MF FI FreeOmegaMixedMeasure bool). intro x.
    apply (@FIProb E SubEnumQ MF FI FreeOmegaMixedMeasure bool). intro y.
    apply (@FIStop E SubEnumQ MF FI FreeOmegaMixedMeasure bool).
Qed.
Lemma exchange_right_cut_valid t u : exchange_retry_pairs t u ->
  @finite_internal E SubEnumQ MF FI FreeOmegaMixedMeasure bool u (exchange_right_cut (t,u)).
Proof.
  intro H. destruct H.
  - exact (@FIStop E SubEnumQ MF FI FreeOmegaMixedMeasure bool exchange_retry_right).
  - apply (@FIProb E SubEnumQ MF FI FreeOmegaMixedMeasure bool). intro y.
    apply (@FIProb E SubEnumQ MF FI FreeOmegaMixedMeasure bool). intro x.
    apply (@FIStop E SubEnumQ MF FI FreeOmegaMixedMeasure bool).
Qed.

Definition exchange_residual_pair x y : Pair :=
  if Bool.eqb x y then (Tau exchange_retry_left, Tau exchange_retry_right)
  else (Ret x, Ret x).
Definition exchange_left_joint (p : Pair) : MF Pair :=
  match observe (fst p) with
  | TauF _ => FORet p
  | _ => FOSample mu (fun x => FOSample nu (fun y => FORet (exchange_residual_pair x y)))
  end.
Definition exchange_right_joint (p : Pair) : MF Pair :=
  match observe (fst p) with
  | TauF _ => FORet p
  | _ => FOSample nu (fun y => FOSample mu (fun x => FORet (exchange_residual_pair x y)))
  end.

Lemma exchange_residual_references t u : exchange_retry_pairs t u ->
  free_omega_coupling_references (fun t u => pstrongF eq exchange_retry_pairs (observe t) (observe u))
    (exchange_left_cut (t,u)) (exchange_right_cut (t,u))
    (exchange_left_joint (t,u)) (exchange_right_joint (t,u)).
Proof.
  intro H. destruct H.
  - split; [apply free_omega_qlift_refl; intro z; reflexivity|].
    split; [apply FOLRet; reflexivity|]. split; [apply FOLRet; reflexivity|].
    apply FOAERet. cbn beta.
    change (PStrong.pstrongF eq exchange_retry_pairs
      (TauF (exchange_left_round exchange_retry_left))
      (TauF (exchange_right_round exchange_retry_right))).
    constructor. constructor.
  - split.
    + apply free_omega_mixed_exchange_of_product.
      * exact (enumQ_semantic_product_swap (subenumQ_raw mu) (subenumQ_raw nu)).
      * intros x y. apply free_omega_qlift_refl. intro z. reflexivity.
    + split.
      * apply FOLSample with (S := eq); [apply sem_lift_refl; intro x; reflexivity|].
        intros x x' ->.
        apply FOLSample with (S := eq); [apply sem_lift_refl; intro y; reflexivity|].
        intros y y' ->. unfold exchange_residual_pair. destruct (Bool.eqb x' y');
          apply FOLRet; reflexivity.
      * split.
        -- apply FOLSample with (S := eq); [apply sem_lift_refl; intro y; reflexivity|].
           intros y y' ->.
           apply FOLSample with (S := eq); [apply sem_lift_refl; intro x; reflexivity|].
           intros x x' ->. unfold exchange_residual_pair. destruct (Bool.eqb x' y');
             apply FOLRet; reflexivity.
        -- apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
           intros x _. apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
           intros y _. apply FOAERet. unfold exchange_residual_pair.
           destruct (Bool.eqb x y); constructor; [constructor|reflexivity].
Qed.

Theorem exchange_inside_unbounded_retry :
  @peutt E SubEnumQ MF FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool bool eq
    exchange_retry_left exchange_retry_right.
Proof.
  eapply peutt_coinduction_finite_internal_coupling_references with
    (sim := exchange_retry_pairs) (cut1 := exchange_left_cut) (cut2 := exchange_right_cut)
    (left_joint := exchange_left_joint) (right_joint := exchange_right_joint).
  - exact exchange_residual_references.
  - exact (@subenumQ_coupling_realization).
  - exact exchange_left_cut_valid.
  - exact exchange_right_cut_valid.
  - constructor.
Qed.

(** This example really exceeds structural residual matching.  Fixing the
    first bit to false while the second bit has both possible values makes
    any structural match compare a returning branch with a Tau branch.
    The behavioral theorem above still applies to these same measures. *)
Example exchange_residuals_not_structural
    (mu_is_dirac : mu = subenumQ_ret false)
    (both_values : forall P, @sem_ae SubEnumQ SubEnumQ_SemanticMeasure bool nu P ->
      P true /\ P false) (sim : tree -> tree -> Prop) :
  ~ free_omega_lift (fun t u => pstrongF eq sim (observe t) (observe u))
    (exchange_left_cut (exchange_left_round exchange_retry_left,
      exchange_right_round exchange_retry_right))
    (exchange_right_cut (exchange_left_round exchange_retry_left,
      exchange_right_round exchange_retry_right)).
Proof.
  intro Hlift.
  change (free_omega_lift (fun t u => pstrongF eq sim (observe t) (observe u))
    (FOSample mu (fun x => FOSample nu
      (fun y => FORet (if Bool.eqb x y then Tau exchange_retry_left else Ret x))))
    (FOSample nu (fun y => FOSample mu
      (fun x => FORet (if Bool.eqb x y then Tau exchange_retry_right else Ret x))))) in Hlift.
  rewrite mu_is_dirac in Hlift.
  dependent destruction Hlift.
  rename S into Top. rename H into Htop. rename H0 into Hbranches.
  assert (Hret : @sem_ae SubEnumQ SubEnumQ_SemanticMeasure bool
    (subenumQ_ret false) (fun x => x = false)).
  { apply (proj2 (@sem_ae_ret_iff SubEnumQ SubEnumQ_SemanticMeasure
      SubEnumQ_SemanticMeasureDiracAELaws bool false (fun x => x = false))). reflexivity. }
  pose proof (sem_lift_ae_transport_r Htop Hret) as Hsupport.
  destruct (proj2 (both_values _ Hsupport)) as [x [Hxf ->]].
  pose proof (Hbranches false false Hxf) as Hsecond.
  dependent destruction Hsecond.
  rename S into Inner. rename H into Hinner. rename H0 into Hleaves.
  pose proof (sem_lift_ae_transport_r (sem_lift_sym Hinner) Hret) as Hinner_support.
  destruct (proj1 (both_values _ Hinner_support)) as [y [Hty ->]].
  pose proof (Hleaves true false Hty) as Hleaf.
  dependent destruction Hleaf. cbn beta in H. inversion H.
Qed.

End ExchangeRetries.

(** Discharge the support premise on an actual probability carrier.  This
    makes the negative structural test non-vacuous: the first coin is Dirac
    false and the second is the same fair SubEnumQ coin used by other tests. *)
Lemma exchange_fair_both_values (P : bool -> Prop) :
  @sem_ae SubEnumQ SubEnumQ_SemanticMeasure bool subenumQ_fair P ->
  P true /\ P false.
Proof.
  intro Hae.
  change (PTree.Prob.Backend.EnumQ.FrontierLift.enumQ_ae reg_fair P) in Hae.
  assert (Hhalf : reg_half <> PTree.Prob.Backend.Common.RatSubTypes.nnQ_0).
  { intro H. apply (f_equal PTree.Prob.Backend.Common.RatSubTypes.Qval) in H. discriminate H. }
  split; apply (Hae reg_half); cbn; auto.
Qed.

Example exchange_fair_retry_equivalent :
  @peutt exchangeE SubEnumQ (FreeOmega SubEnumQ)
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool bool eq
    (exchange_retry_left (subenumQ_ret false) subenumQ_fair)
    (exchange_retry_right (subenumQ_ret false) subenumQ_fair).
Proof. apply exchange_inside_unbounded_retry. Qed.

Example exchange_fair_residuals_not_structural
    (sim : ptree exchangeE SubEnumQ bool -> ptree exchangeE SubEnumQ bool -> Prop) :
  let mu := subenumQ_ret false in
  let nu := subenumQ_fair in
  let left := exchange_left_round mu nu (exchange_retry_left mu nu) in
  let right := exchange_right_round mu nu (exchange_retry_right mu nu) in
  ~ free_omega_lift (fun t u => pstrongF eq sim (observe t) (observe u))
    (exchange_left_cut mu nu (left,right))
    (exchange_right_cut mu nu (left,right)).
Proof.
  apply exchange_residuals_not_structural; [reflexivity|].
  exact exchange_fair_both_values.
Qed.
