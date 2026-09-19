Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Prob Require Import TwoLevelMeasure SemanticCoupling
  FreeOmegaMeasure FreeOmegaNative.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Extend an ACTUAL latent joint by dependent native conditional joints.
    Its marginal certificates may live only in the quotient.  This is
    the construction needed to append matched guards to recovered cuts;
    it is not an extraction theorem for arbitrary quotient couplings. *)
Section Extension.
Universes node node_rep frontier.
Context {MN : Type@{node} -> Type@{node_rep}}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}.
Context {Anchor : Type@{frontier}}.
Local Notation qlift := (@free_omega_qlift@{
  frontier frontier node node node node node node node node node node frontier frontier frontier
  node node node node node_rep node node node node node node node node
  node node node node node node node node node node} MN NI NO _ _).

Lemma native_sigma_identity {X : Type@{node}} {Y : X -> Type@{node}}
    (mu : MN X) (k : forall x, MN (Y x)) :
  qlift eq
    (FOSample mu (fun x => FOSample (k x) (fun y => FORet (existT Y x y))) :
      FreeOmegaAt MN Anchor {x : X & Y x})
    (FOSample (sem_bind mu (fun x => sem_bind (k x) (fun y => sem_ret (existT Y x y))))
      (fun z => FORet z)).
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
Variable left : Z -> X.
Variable right : Z -> Y.
Variable Good : Z -> Prop.
Variable U : X -> Type@{node}.
Variable V : Y -> Type@{node}.
Variable left_kernel : forall x, MN (U x).
Variable right_kernel : forall y, MN (V y).
Variable conditional : forall z, MN (U (left z) * V (right z)).
Variable related : forall z, U (left z) -> V (right z) -> Prop.
Arguments related z _ _ : clear implicits.

Hypothesis joint_left : qlift (fun z x => left z = x)
  (FOSample joint (fun z => FORet z)) (FOSample mu (fun x => FORet x)).
Hypothesis joint_right : qlift (fun z y => right z = y)
  (FOSample joint (fun z => FORet z)) (FOSample nu (fun y => FORet y)).
Hypothesis joint_good : sem_ae joint Good.
Hypothesis conditional_joint : forall z, Good z ->
  semantic_coupling (related z) (left_kernel (left z)) (right_kernel (right z))
    (conditional z).

Definition extended_joint_path : Type@{node} :=
  {z : Z & (U (left z) * V (right z))%type}.
Definition extended_joint_measure : MN extended_joint_path :=
  sem_bind joint (fun z => sem_bind (conditional z)
    (fun uv => sem_ret (existT _ z uv))).
Definition extended_joint_left (w : extended_joint_path) : {x : X & U x} :=
  existT U (left (projT1 w)) (fst (projT2 w)).
Definition extended_joint_right (w : extended_joint_path) : {y : Y & V y} :=
  existT V (right (projT1 w)) (snd (projT2 w)).
Definition extended_left_measure : MN {x : X & U x} :=
  sem_bind mu (fun x => sem_bind (left_kernel x) (fun u => sem_ret (existT U x u))).
Definition extended_right_measure : MN {y : Y & V y} :=
  sem_bind nu (fun y => sem_bind (right_kernel y) (fun v => sem_ret (existT V y v))).

Let joint_nested : FreeOmegaAt MN Anchor extended_joint_path :=
  FOSample joint (fun z => FOSample (conditional z) (fun uv => FORet (existT _ z uv))).
Let left_nested : FreeOmegaAt MN Anchor {x : X & U x} :=
  FOSample mu (fun x => FOSample (left_kernel x) (fun u => FORet (existT U x u))).
Let right_nested : FreeOmegaAt MN Anchor {y : Y & V y} :=
  FOSample nu (fun y => FOSample (right_kernel y) (fun v => FORet (existT V y v))).

Lemma extended_joint_support : sem_ae extended_joint_measure (fun w =>
  Good (projT1 w) /\ related (projT1 w) (fst (projT2 w)) (snd (projT2 w))).
Proof.
  apply sem_ae_bind_iff. eapply sem_ae_mono; [|exact joint_good].
  intros z Hz. apply sem_ae_bind_iff.
  eapply sem_ae_mono; [|exact (proj2 (proj2 (conditional_joint Hz)))].
  intros [u v] Huv. apply sem_ae_ret_iff. split; assumption.
Qed.

Lemma extended_joint_nested_left :
  qlift (fun w x => extended_joint_left w = x) joint_nested left_nested.
Proof.
  change (qlift (fun w x => extended_joint_left w = x)
    (free_omega_bind (FOSample joint (fun z => FORet z))
      (fun z => FOSample (conditional z) (fun uv => FORet (existT _ z uv))))
    (free_omega_bind (FOSample mu (fun x => FORet x))
      (fun x => FOSample (left_kernel x) (fun u => FORet (existT U x u))))).
  eapply FOQLBind with (T := fun z x => left z = x /\ Good z).
  - eapply FOQLAERestrict with (T := fun z x => left z = x)
      (P := Good) (Q := fun _ => True).
    + exact joint_left.
    + apply FOAESample with (Good := Good); [exact joint_good|].
      intros z Hz. apply FOAERet. exact Hz.
    + apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
      intros x _. apply FOAERet. exact I.
    + intros z x [Heq [Hz _]]. split; assumption.
  - intros z x [<- Hz].
    eapply FOQLSample; [exact (proj1 (conditional_joint Hz))|].
    intros [u v] u' Hu. apply FOQLStructural, FOLRet.
    cbn in Hu |- *. subst u'. reflexivity.
Qed.

Lemma extended_joint_nested_right :
  qlift (fun w y => extended_joint_right w = y) joint_nested right_nested.
Proof.
  change (qlift (fun w y => extended_joint_right w = y)
    (free_omega_bind (FOSample joint (fun z => FORet z))
      (fun z => FOSample (conditional z) (fun uv => FORet (existT _ z uv))))
    (free_omega_bind (FOSample nu (fun y => FORet y))
      (fun y => FOSample (right_kernel y) (fun v => FORet (existT V y v))))).
  eapply FOQLBind with (T := fun z y => right z = y /\ Good z).
  - eapply FOQLAERestrict with (T := fun z y => right z = y)
      (P := Good) (Q := fun _ => True).
    + exact joint_right.
    + apply FOAESample with (Good := Good); [exact joint_good|].
      intros z Hz. apply FOAERet. exact Hz.
    + apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
      intros y _. apply FOAERet. exact I.
    + intros z y [Heq [Hz _]]. split; assumption.
  - intros z y [<- Hz].
    eapply FOQLSample; [exact (proj1 (proj2 (conditional_joint Hz)))|].
    intros [u v] v' Hv. apply FOQLStructural, FOLRet.
    cbn in Hv |- *. subst v'. reflexivity.
Qed.

Theorem extended_joint_left_marginal :
  qlift (fun w x => extended_joint_left w = x)
    (FOSample extended_joint_measure (fun w => FORet w))
    (FOSample extended_left_measure (fun x => FORet x)).
Proof.
  eapply FOQLComp with (T := eq) (U := fun w x => extended_joint_left w = x)
    (mid := joint_nested).
  - apply FOQLMono with (T := fun x y => y = x).
    + apply FOQLSym, native_sigma_identity.
    + intros x y Hyx. symmetry. exact Hyx.
  - eapply FOQLComp with (T := fun w x => extended_joint_left w = x) (U := eq)
      (mid := left_nested).
    + apply extended_joint_nested_left.
    + apply native_sigma_identity.
    + intros w z [x [Hx ->]]. exact Hx.
  - intros w z [x [-> Hx]]. exact Hx.
Qed.

Theorem extended_joint_right_marginal :
  qlift (fun w y => extended_joint_right w = y)
    (FOSample extended_joint_measure (fun w => FORet w))
    (FOSample extended_right_measure (fun y => FORet y)).
Proof.
  eapply FOQLComp with (T := eq) (U := fun w y => extended_joint_right w = y)
    (mid := joint_nested).
  - apply FOQLMono with (T := fun x y => y = x).
    + apply FOQLSym, native_sigma_identity.
    + intros x y Hyx. symmetry. exact Hyx.
  - eapply FOQLComp with (T := fun w y => extended_joint_right w = y) (U := eq)
      (mid := right_nested).
    + apply extended_joint_nested_right.
    + apply native_sigma_identity.
    + intros w z [y [Hy ->]]. exact Hy.
  - intros w z [y [-> Hy]]. exact Hy.
Qed.
End Extension.
