(** Bind extraction contracts: approximation is not quotient equality;
    one generic congruence serves arbitrary return carriers and relations. *)
Set Universe Polymorphism.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed BindOrder.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation
  PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure
  PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.BindOrder.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import PEutt Bind BindScheduling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NegativeOrderBoundary.
Context {MN : Type -> Type} `{NI : SemanticMeasure MN} `{NO : @SemanticOmega MN NI}.

Example constant_lub_quotient_equal :
  free_omega_qlift eq (@FORet MN unit tt) (FOLub (fun _ => FORet tt)).
Proof. apply FOQLLubConstantR, FOQLStructural; constructor; reflexivity. Qed.

Example constant_lub_not_approx_forward :
  ~ free_omega_approx eq (@FORet MN unit tt) (FOLub (fun _ => FORet tt)).
Proof. intro H; inversion H. Qed.

Example constant_lub_not_approx_backward :
  ~ free_omega_approx eq (FOLub (fun _ => @FORet MN unit tt)) (FORet tt).
Proof. intro H; inversion H. Qed.

Example observable_equality_does_not_imply_order :
  ~ (forall (mu nu : FreeOmega MN unit),
    @sem_eq (FreeOmega MN) (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)) _ mu nu ->
    @sem_le (FreeOmega MN) (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmega _ mu nu).
Proof.
  cbn. intro H. apply constant_lub_not_approx_forward.
  apply H, constant_lub_quotient_equal.
Qed.

Example sampled_zero_quotient_equal {A B} (mu : MN A) :
  free_omega_qlift (@eq B) (FOSample mu (fun _ => FOZero)) FOZero.
Proof. apply FOQLSampleZero. Qed.

Example sampled_zero_not_approx_bottom {A B} (mu : MN A) :
  ~ free_omega_approx (@eq B) (FOSample mu (fun _ => FOZero)) FOZero.
Proof. intro H; inversion H. Qed.
End NegativeOrderBoundary.

(** Audit the actual generic theorem: no FreeOmega, MathComp, native measure
    laws, Fubini, mixed omega continuity, or global choice in its signature. *)
Definition generic_bind_endpoint := @PTree.Eq.Bind.peutt_bind.
Definition generic_scheduling_endpoint := @BindScheduling.ptree_bind_cofinal_all.

Section FreeOmegaClient.
Context {E MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI} `{NO : @SemanticOmega MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation W := (@peutt E MN MF FI FC FreeOmegaMixedMeasure FO).

Example free_omega_heterogeneous_bind {A B X Y}
    (RR : X -> Y -> Prop) (RS : A -> B -> Prop)
    (t : ptree E MN X) (u : ptree E MN Y)
    (k : X -> ptree E MN A) (h : Y -> ptree E MN B) :
  W RR t u -> (forall x y, RR x y -> W RS (k x) (h y)) ->
  W RS (PTree.bind t k) (PTree.bind u h).
Proof. intros Ht Hk; eapply peutt_bind; eassumption. Qed.
End FreeOmegaClient.
