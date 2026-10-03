(** Role: Canonical FreeOmega measure infrastructure. Depends on generic measures; not a concrete native backend or program equivalence. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed PTree.Prob.Interface.SemanticCoupling.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Native.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Extend an ACTUAL latent joint by dependent native conditional joints.
    Its marginal certificates may live only in the quotient.  This is
    the construction needed to append matched guards to recovered cuts;
    it is not an extraction theorem for arbitrary quotient couplings. *)
Section Extension.
Universes node node_rep frontier.
Context {MN : Type@{node} → Type@{node_rep}}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}.
Context {Anchor : Type@{frontier}}.
Local Notation qlift := (@free_omega_qlift@{
  frontier frontier node node node node node node node node node node frontier frontier frontier
  node node node node node_rep node node node node node node node node
  node node node node node node node node node node} MN NI NO _ _).

Lemma native_sigma_identity {X : Type@{node}} {Y : X → Type@{node}}
    (mu : MN X) (k : ∀ x, MN (Y x)) :
  qlift eq
    (FOSample mu (λ x, FOSample (k x) (λ y, FORet (existT Y x y))) :
      FreeOmegaAt MN Anchor {x : X & Y x})
    (FOSample (sem_bind mu (λ x, sem_bind (k x) (λ y, sem_ret (existT Y x y))))
      (λ z, FORet z)).
Proof.
  eapply FOQLComp with (T := eq) (U := eq).
  - apply free_omega_sample_sigma.
  - eapply FOQLSample with (T := eq); [apply sem_lift_refl; intro x; reflexivity|].
    intros x y ->. destruct y. apply FOQLStructural, FOLRet. reflexivity.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

Context {X Y Z : Type@{node}}.
Variable mu : MN X.
Variable nu : MN Y.
Variable joint : MN Z.
Variable left : Z → X.
Variable right : Z → Y.
Variable Good : Z → Prop.
Variable U : X → Type@{node}.
Variable V : Y → Type@{node}.
Variable left_kernel : ∀ x, MN (U x).
Variable right_kernel : ∀ y, MN (V y).
Variable conditional : ∀ z, MN (U (left z) * V (right z)).
Variable related : ∀ z, U (left z) → V (right z) → Prop.
Arguments related z _ _ : clear implicits.

Hypothesis joint_left : qlift (λ z x, left z = x)
  (FOSample joint (λ z, FORet z)) (FOSample mu (λ x, FORet x)).
Hypothesis joint_right : qlift (λ z y, right z = y)
  (FOSample joint (λ z, FORet z)) (FOSample nu (λ y, FORet y)).
Hypothesis joint_good : sem_ae joint Good.
Hypothesis conditional_joint : ∀ z, Good z →
  semantic_coupling (related z) (left_kernel (left z)) (right_kernel (right z))
    (conditional z).

Definition extended_joint_path : Type@{node} :=
  {z : Z & (U (left z) * V (right z))%type}.
Definition extended_joint_measure : MN extended_joint_path :=
  sem_bind joint (λ z, sem_bind (conditional z)
    (λ uv, sem_ret (existT _ z uv))).
Definition extended_joint_left (w : extended_joint_path) : {x : X & U x} :=
  existT U (left (projT1 w)) (fst (projT2 w)).
Definition extended_joint_right (w : extended_joint_path) : {y : Y & V y} :=
  existT V (right (projT1 w)) (snd (projT2 w)).
Definition extended_left_measure : MN {x : X & U x} :=
  sem_bind mu (λ x, sem_bind (left_kernel x) (λ u, sem_ret (existT U x u))).
Definition extended_right_measure : MN {y : Y & V y} :=
  sem_bind nu (λ y, sem_bind (right_kernel y) (λ v, sem_ret (existT V y v))).

Let joint_nested : FreeOmegaAt MN Anchor extended_joint_path :=
  FOSample joint (λ z, FOSample (conditional z) (λ uv, FORet (existT _ z uv))).
Let left_nested : FreeOmegaAt MN Anchor {x : X & U x} :=
  FOSample mu (λ x, FOSample (left_kernel x) (λ u, FORet (existT U x u))).
Let right_nested : FreeOmegaAt MN Anchor {y : Y & V y} :=
  FOSample nu (λ y, FOSample (right_kernel y) (λ v, FORet (existT V y v))).

Lemma extended_joint_support : sem_ae extended_joint_measure (λ w,
  Good (projT1 w) ∧ related (projT1 w) (fst (projT2 w)) (snd (projT2 w))).
Proof.
  apply sem_ae_bind_iff. eapply sem_ae_mono; [|exact joint_good].
  intros z Hz. apply sem_ae_bind_iff.
  eapply sem_ae_mono; [|exact (proj2 (proj2 (conditional_joint Hz)))].
  intros [u v] Huv. apply sem_ae_ret_iff. split; assumption.
Qed.

Lemma extended_joint_nested_left :
  qlift (λ w x, extended_joint_left w = x) joint_nested left_nested.
Proof.
  change (qlift (λ w x, extended_joint_left w = x)
    (free_omega_bind (FOSample joint (λ z, FORet z))
      (λ z, FOSample (conditional z) (λ uv, FORet (existT _ z uv))))
    (free_omega_bind (FOSample mu (λ x, FORet x))
      (λ x, FOSample (left_kernel x) (λ u, FORet (existT U x u))))).
  eapply FOQLBind with (T := λ z x, left z = x ∧ Good z).
  - eapply FOQLAERestrict with (T := λ z x, left z = x)
      (P := Good) (Q := λ _, True).
    + exact joint_left.
    + apply FOAESample with (Good := Good); [exact joint_good|].
      intros z Hz. apply FOAERet. exact Hz.
    + apply FOAESample with (Good := λ _, True); [apply sem_ae_true|].
      intros x _. apply FOAERet. exact I.
    + intros z x [Heq [Hz _]]. split; assumption.
  - intros z x [<- Hz].
    eapply FOQLSample; [exact (proj1 (conditional_joint Hz))|].
    intros [u v] u' Hu. apply FOQLStructural, FOLRet.
    cbn in Hu |- *. subst u'. reflexivity.
Qed.

Lemma extended_joint_nested_right :
  qlift (λ w y, extended_joint_right w = y) joint_nested right_nested.
Proof.
  change (qlift (λ w y, extended_joint_right w = y)
    (free_omega_bind (FOSample joint (λ z, FORet z))
      (λ z, FOSample (conditional z) (λ uv, FORet (existT _ z uv))))
    (free_omega_bind (FOSample nu (λ y, FORet y))
      (λ y, FOSample (right_kernel y) (λ v, FORet (existT V y v))))).
  eapply FOQLBind with (T := λ z y, right z = y ∧ Good z).
  - eapply FOQLAERestrict with (T := λ z y, right z = y)
      (P := Good) (Q := λ _, True).
    + exact joint_right.
    + apply FOAESample with (Good := Good); [exact joint_good|].
      intros z Hz. apply FOAERet. exact Hz.
    + apply FOAESample with (Good := λ _, True); [apply sem_ae_true|].
      intros y _. apply FOAERet. exact I.
    + intros z y [Heq [Hz _]]. split; assumption.
  - intros z y [<- Hz].
    eapply FOQLSample; [exact (proj1 (proj2 (conditional_joint Hz)))|].
    intros [u v] v' Hv. apply FOQLStructural, FOLRet.
    cbn in Hv |- *. subst v'. reflexivity.
Qed.

Theorem extended_joint_left_marginal :
  qlift (λ w x, extended_joint_left w = x)
    (FOSample extended_joint_measure (λ w, FORet w))
    (FOSample extended_left_measure (λ x, FORet x)).
Proof.
  eapply FOQLComp with (T := eq) (U := λ w x, extended_joint_left w = x)
    (mid := joint_nested).
  - apply FOQLMono with (T := λ x y, y = x).
    + apply FOQLSym, native_sigma_identity.
    + intros x y Hyx. symmetry. exact Hyx.
  - eapply FOQLComp with (T := λ w x, extended_joint_left w = x) (U := eq)
      (mid := left_nested).
    + apply extended_joint_nested_left.
    + apply native_sigma_identity.
    + intros w z [x [Hx ->]]. exact Hx.
  - intros w z [x [-> Hx]]. exact Hx.
Qed.

Theorem extended_joint_right_marginal :
  qlift (λ w y, extended_joint_right w = y)
    (FOSample extended_joint_measure (λ w, FORet w))
    (FOSample extended_right_measure (λ y, FORet y)).
Proof.
  eapply FOQLComp with (T := eq) (U := λ w y, extended_joint_right w = y)
    (mid := joint_nested).
  - apply FOQLMono with (T := λ x y, y = x).
    + apply FOQLSym, native_sigma_identity.
    + intros x y Hyx. symmetry. exact Hyx.
  - eapply FOQLComp with (T := λ w y, extended_joint_right w = y) (U := eq)
      (mid := right_nested).
    + apply extended_joint_nested_right.
    + apply native_sigma_identity.
    + intros w z [y [Hy ->]]. exact Hy.
  - intros w z [y [-> Hy]]. exact Hy.
Qed.
End Extension.
