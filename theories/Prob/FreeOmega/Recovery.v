(** Role: Canonical FreeOmega measure infrastructure. Depends on generic measures; not a concrete native backend or program equivalence. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Native.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Recovering latent sample paths from a decoded value is a conditional
    resampling problem, not a choice of one supported preimage.  All
    reconstruction and normalization laws below live in the quotient;
    no reflection from quotient coupling to node lifting is assumed. *)
Section Recovery.
Universes node node_rep frontier.
Context {MN : Type@{node} -> Type@{node_rep}}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}.

(** Fix the intermediate carriers of quotient composition/bind at the
    frontier universe.  A recovery crosses from high decoded values back
    to small paths; specializing these intermediate universes to the node
    universe would make an otherwise valid certificate unusable by bind.
    This notation is exactly the existing quotient judgment. *)
Local Notation qlift := (@free_omega_qlift@{
  frontier frontier node node node node node node node node node node frontier frontier frontier
  node node node node node_rep node node node node node node node node
  node node node node node node node node node node} MN NI NO _ _).

Record free_omega_native_recovery {A : Type@{frontier}}
    (p : free_omega_native_presentation@{node node_rep frontier} MN A) := {
  recovery_good : A -> Prop;
  recovery_kernel : A -> FreeOmegaAt MN A (native_sample_type p);
  recovery_good_ae : free_omega_ae recovery_good (free_omega_native p);
  recovery_fiber : forall a, recovery_good a ->
    free_omega_ae (fun x => native_sample_value p x = a) (recovery_kernel a);
  recovery_normalized : forall a, recovery_good a ->
    qlift (fun _ _ => True) (recovery_kernel a) (FORet tt);
  recovery_reconstruct : qlift eq
    (free_omega_bind (free_omega_native p) recovery_kernel)
    (FOSample (native_sample_measure p) (fun x => FORet x) :
      FreeOmegaAt MN A (native_sample_type p))
}.

Lemma recovery_branch_coupling {A B : Type@{frontier}}
    {p : free_omega_native_presentation MN A}
    {q : free_omega_native_presentation MN B}
    (dp : free_omega_native_recovery p) (dq : free_omega_native_recovery q)
    (R : A -> B -> Prop) a b :
  R a b -> recovery_good dp a -> recovery_good dq b ->
  qlift (fun x y => R (native_sample_value p x) (native_sample_value q y))
    (recovery_kernel dp a) (recovery_kernel dq b).
Proof.
  intros HR Ha Hb.
  eapply FOQLAERestrict with (T := fun _ _ => True)
    (P := fun x => native_sample_value p x = a)
    (Q := fun y => native_sample_value q y = b).
  - eapply FOQLComp with (T := fun _ _ => True) (U := fun _ _ => True)
      (mid := FORet tt).
    + apply recovery_normalized. exact Ha.
    + apply FOQLSym. apply recovery_normalized. exact Hb.
    + intros x y _. exact I.
  - apply recovery_fiber. exact Ha.
  - apply recovery_fiber. exact Hb.
  - intros x y [_ [-> ->]]. exact HR.
Qed.

(** Pull back a decoded coupling to the ACTUAL sample spaces, preserving
    the complete marginal distributions rather than choosing partners.
    Recovery data is individual to each presentation and independent of R. *)
Theorem free_omega_native_coupling_pullback {A B : Type@{frontier}}
    {p : free_omega_native_presentation MN A}
    {q : free_omega_native_presentation MN B}
    (dp : free_omega_native_recovery p) (dq : free_omega_native_recovery q)
    (R : A -> B -> Prop) :
  qlift R (free_omega_native p) (free_omega_native q) ->
  qlift (fun x y => R (native_sample_value p x) (native_sample_value q y))
    (FOSample (native_sample_measure p) (fun x => FORet x) :
      FreeOmegaAt MN A (native_sample_type p))
    (FOSample (native_sample_measure q) (fun y => FORet y) :
      FreeOmegaAt MN B (native_sample_type q)).
Proof.
  intro Hrel.
  eapply FOQLComp with (T := eq)
    (U := fun x y => R (native_sample_value p x) (native_sample_value q y))
    (mid := free_omega_bind (free_omega_native p) (recovery_kernel dp)).
  - apply FOQLMono with (T := fun x y => y = x).
    + apply FOQLSym. apply recovery_reconstruct.
    + intros x y Hyx. symmetry. exact Hyx.
  - eapply FOQLComp with
      (T := fun x y => R (native_sample_value p x) (native_sample_value q y))
      (U := eq)
      (mid := free_omega_bind (free_omega_native q) (recovery_kernel dq)).
    + eapply FOQLBind with
        (T := fun a b => R a b /\ recovery_good dp a /\ recovery_good dq b).
      * eapply FOQLAERestrict; [exact Hrel|apply recovery_good_ae|apply recovery_good_ae|].
        intros a b H. exact H.
      * intros a b [HR [Ha Hb]]. apply recovery_branch_coupling; assumption.
    + apply recovery_reconstruct.
    + intros x z [y [Hxy ->]]. exact Hxy.
  - intros x z [y [-> Hyz]]. exact Hyz.
Qed.

(** A constant decoder must recover ALL latent randomness.  Resampling
    the original total sample is a recovery; selecting one preimage would
    not in general satisfy the reconstruction field. *)
Definition constant_native_presentation {X : Type@{node}} {A : Type@{frontier}} (mu : MN X) (a : A) :
    free_omega_native_presentation MN A :=
  {| native_sample_type := X; native_sample_measure := mu;
     native_sample_value := fun _ => a |}.

Lemma constant_native_collapse {X : Type@{node}} {A : Type@{frontier}} (mu : MN X) (a : A) :
  qlift (fun _ _ => True)
    (FOSample mu (fun x => FORet x) : FreeOmegaAt MN A X)
    (FORet tt : FreeOmegaAt MN A unit) ->
  qlift eq (free_omega_native (constant_native_presentation mu a)) (FORet a).
Proof.
  intro Htotal.
  change (qlift eq
    (free_omega_bind (FOSample mu (fun x => FORet x)) (fun _ => FORet a))
    (free_omega_bind (FORet tt) (fun _ => FORet a))).
  eapply FOQLBind; [exact Htotal|].
  intros x y _. apply FOQLStructural, FOLRet. reflexivity.
Qed.

Definition constant_native_recovery {X : Type@{node}} {A : Type@{frontier}} (mu : MN X) (a : A)
    (Htotal : qlift (fun _ _ => True)
      (FOSample mu (fun x => FORet x) : FreeOmegaAt MN A X)
      (FORet tt : FreeOmegaAt MN A unit)) :
    free_omega_native_recovery (constant_native_presentation mu a).
Proof.
  refine (@Build_free_omega_native_recovery A (constant_native_presentation mu a)
    (fun b => b = a) (fun _ => FOSample mu (fun x => FORet x)) _ _ _ _).
  - apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros x _. apply FOAERet. reflexivity.
  - intros b ->. apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros x _. apply FOAERet. reflexivity.
  - intros b _. exact Htotal.
  - change (qlift eq
      (free_omega_bind (FOSample mu (fun x => FORet x))
        (fun _ => FOSample mu (fun x => FORet x)))
      (free_omega_bind (FORet tt) (fun _ => FOSample mu (fun x => FORet x)))).
    eapply FOQLBind; [exact Htotal|].
    intros x y _. apply free_omega_qlift_refl. intro z. reflexivity.
Defined.

(** An actual inverse is the special case with deterministic recovery.
    No totality assumption on the ORIGINAL measure is needed. *)
Definition inverse_native_recovery {A : Type@{frontier}} (p : free_omega_native_presentation MN A)
    (inverse : A -> native_sample_type p)
    (Hinverse : forall x, inverse (native_sample_value p x) = x) :
    free_omega_native_recovery p.
Proof.
  refine (@Build_free_omega_native_recovery A p
    (fun a => native_sample_value p (inverse a) = a)
    (fun a => FORet (inverse a)) _ _ _ _).
  - apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros x _. apply FOAERet. rewrite Hinverse. reflexivity.
  - intros a Ha. apply FOAERet. exact Ha.
  - intros a _. apply FOQLStructural, FOLRet. exact I.
  - cbn [free_omega_native free_omega_bind]. eapply FOQLSample with (T := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. apply FOQLStructural, FOLRet. apply Hinverse.
Defined.
End Recovery.
