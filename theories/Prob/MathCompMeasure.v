Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Morphisms.

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets functions cardinality reals
  fsbigop.
From mathcomp.analysis Require Import measure probability kernel
  measurable_realfun ereal numfun.

From PTree.Prob Require Import FrontierLift MeasureIteration.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** A uniform discrete measurable carrier for an arbitrary Coq type.  The
    extra [MCBottom] point is needed because MathComp's [measurableType]
    hierarchy is pointed/choice-based, whereas [MeasureInterface] ranges over
    every [Type], including empty ones. *)
Variant mc_carrier (A : Type) : Type :=
  | MCBottom
  | MCValue (value : A).

Arguments MCBottom {A}.
Arguments MCValue {A} _.

HB.instance Definition _ A := gen_eqMixin (mc_carrier A).
HB.instance Definition _ A := gen_choiceMixin (mc_carrier A).
HB.instance Definition _ A := isPointed.Build (mc_carrier A) MCBottom.

HB.instance Definition _ A := @isMeasurable.Build default_measure_display
  (mc_carrier A) discrete_measurable discrete_measurable0
  discrete_measurableC discrete_measurableU.

(** A coupling uses its own fully discrete joint carrier.  This is
    intentionally not MathComp's product measurable structure: the abstract
    lifting accepts arbitrary Coq relations, and on infinite spaces such a
    relation need not belong to the product sigma-algebra. *)
Variant mc_joint (A B : Type) : Type :=
  | MCJoint (joint_left : mc_carrier A) (joint_right : mc_carrier B).

Arguments MCJoint {A B} _ _.

HB.instance Definition _ A B := gen_eqMixin (mc_joint A B).
HB.instance Definition _ A B := gen_choiceMixin (mc_joint A B).
HB.instance Definition _ A B := isPointed.Build (mc_joint A B)
  (MCJoint MCBottom MCBottom).
HB.instance Definition _ A B := @isMeasurable.Build default_measure_display
  (mc_joint A B) discrete_measurable discrete_measurable0
  discrete_measurableC discrete_measurableU.

Definition mc_joint_fst {A B} (xy : mc_joint A B) : mc_carrier A :=
  match xy with MCJoint x _ => x end.

Definition mc_joint_snd {A B} (xy : mc_joint A B) : mc_carrier B :=
  match xy with MCJoint _ y => y end.

Definition mc_joint_diagonal (A : Type) (x : mc_carrier A) : mc_joint A A :=
  MCJoint x x.
Arguments mc_joint_diagonal A _ : clear implicits.

Section BackendShape.
Context (R : realType).

(** Candidate carrier for the MathComp-Analysis backend.  Bind will be
    integration/composition of subprobability kernels; [MCBottom] represents
    no returned value and therefore accounts for lost mass. *)
Definition MathCompMeasure (A : Type) : Type :=
  subprobability (mc_carrier A) R.

Definition mathcomp_measure_set (A : Type) :=
  classical_sets.set (mc_carrier A).

Definition mathcomp_measure_ret {A} (x : A) :
    subprobability (mc_carrier A) R :=
  [the subprobability (mc_carrier A) R of dirac (MCValue x)].

Definition mathcomp_bottom_measure {A} :
    subprobability (mc_carrier A) R :=
  [the subprobability (mc_carrier A) R of dirac MCBottom].

(** Extend a continuation to the bookkeeping bottom point.  Lost mass is
    propagated as a Dirac mass at bottom; ordinary values use the supplied
    subprobability continuation. *)
Definition mathcomp_extend {A B}
    (k : A -> subprobability (mc_carrier B) R)
    (x : mc_carrier A) : subprobability (mc_carrier B) R :=
  match x with
  | MCBottom => mathcomp_bottom_measure
  | MCValue a => k a
  end.

Definition mathcomp_extend_measure {A B}
    (k : A -> subprobability (mc_carrier B) R)
    (x : mc_carrier A) : measure (mc_carrier B) R :=
  mathcomp_extend k x.

Lemma measurable_mathcomp_extend {A B}
    (k : A -> subprobability (mc_carrier B) R) U :
  measurable U -> measurable_fun [set: mc_carrier A]
    (fun x => mathcomp_extend_measure k x U).
Proof.
  move=> mtop Y mY.
  by [].
Qed.

HB.instance Definition mathcomp_extend_is_kernel {A B}
    (k : A -> subprobability (mc_carrier B) R) :=
  @isKernel.Build _ _ (mc_carrier A) (mc_carrier B) R
    (mathcomp_extend_measure k) (measurable_mathcomp_extend k).

Lemma mathcomp_extend_subprobability {A B}
    (k : A -> subprobability (mc_carrier B) R) :
  ereal_sup [set mathcomp_extend_measure k x [set: mc_carrier B]
    | x in [set: mc_carrier A]] <= 1.
Proof.
  apply/(sprob_kernelP (mathcomp_extend_measure k)).
  move=> [|a]; exact: sprobability_setT.
Qed.

HB.instance Definition mathcomp_extend_is_subprobability_kernel {A B}
    (k : A -> subprobability (mc_carrier B) R) :=
  Kernel_isSubProbability.Build _ _ _ _ R
    (mathcomp_extend_measure k) (mathcomp_extend_subprobability k).

Definition mathcomp_extend_kernel {A B}
    (k : A -> subprobability (mc_carrier B) R) :
    R.-spker (mc_carrier A) ~> (mc_carrier B) :=
  [the R.-spker (mc_carrier A) ~> (mc_carrier B) of
    mathcomp_extend_measure k].

Definition mathcomp_source_measure {A}
    (mu : subprobability (mc_carrier A) R)
    (_ : mc_carrier unit) : measure (mc_carrier A) R := mu.

Lemma measurable_mathcomp_source {A}
    (mu : subprobability (mc_carrier A) R) U :
  measurable U -> measurable_fun [set: mc_carrier unit]
    (fun x => mathcomp_source_measure mu x U).
Proof. move=> mU mtop Y mY. by []. Qed.

HB.instance Definition mathcomp_source_is_kernel {A}
    (mu : subprobability (mc_carrier A) R) :=
  @isKernel.Build _ _ (mc_carrier unit) (mc_carrier A) R
    (mathcomp_source_measure mu) (measurable_mathcomp_source mu).

Lemma mathcomp_source_subprobability {A}
    (mu : subprobability (mc_carrier A) R) :
  ereal_sup [set mathcomp_source_measure mu x [set: mc_carrier A]
    | x in [set: mc_carrier unit]] <= 1.
Proof.
  apply/(sprob_kernelP (mathcomp_source_measure mu)).
  move=> x. exact: sprobability_setT.
Qed.

HB.instance Definition mathcomp_source_is_subprobability_kernel {A}
    (mu : subprobability (mc_carrier A) R) :=
  Kernel_isSubProbability.Build _ _ _ _ R
    (mathcomp_source_measure mu) (mathcomp_source_subprobability mu).

Definition mathcomp_source_kernel {A}
    (mu : subprobability (mc_carrier A) R) :
    R.-spker (mc_carrier unit) ~> (mc_carrier A) :=
  [the R.-spker (mc_carrier unit) ~> (mc_carrier A) of
    mathcomp_source_measure mu].

(** Extensional equality on measurable sets. *)
Definition mathcomp_measure_eq {A}
    (mu nu : measure (mc_carrier A) R) : Prop :=
  forall U : set (mc_carrier A), measurable U -> mu U = nu U.

(** A predicate on returned values is lifted to the carrier by declaring
    the bookkeeping bottom point valid.  Consequently missing mass never
    falsifies an almost-everywhere assertion about returned values. *)
Definition mc_predicate {A} (P : A -> Prop) : set (mc_carrier A) :=
  [set x | match x with MCBottom => True | MCValue a => P a end].

Definition mathcomp_measure_ae {A}
    (mu : measure (mc_carrier A) R) (P : A -> Prop) : Prop :=
  almost_everywhere mu (mc_predicate P).

(** Relations used by couplings also relate the two bottom points.  A
    one-sided bottom point is deliberately unrelated: it would represent a
    mismatch in lost mass. *)
Definition mc_relation {A B} (rel : A -> B -> Prop) :
    set (mc_joint A B) :=
  [set xy | match xy with
   | MCJoint MCBottom MCBottom => True
   | MCJoint (MCValue a) (MCValue b) => rel a b
   | _ => False
   end].

Definition mathcomp_coupling {A B} (rel : A -> B -> Prop)
    (mu : measure (mc_carrier A) R)
    (nu : measure (mc_carrier B) R) : Prop :=
  exists joint : subprobability (mc_joint A B) R,
    (forall U : set (mc_carrier A), measurable U -> ~ U MCBottom ->
      joint (mc_joint_fst @^-1` U) = mu U) /\
    (forall V : set (mc_carrier B), measurable V -> ~ V MCBottom ->
      joint (mc_joint_snd @^-1` V) = nu V) /\
    almost_everywhere joint (mc_relation rel).

(** The intended [MeasureInterface] lifting is existence of a subprobability
    coupling concentrated almost everywhere on the lifted relation. *)
Definition mathcomp_measure_lift {A B} (rel : A -> B -> Prop)
    (mu : measure (mc_carrier A) R)
    (nu : measure (mc_carrier B) R) : Prop :=
  mathcomp_coupling rel mu nu.

(** ** Closed kernel carrier

    MathComp exposes composition as a subprobability *kernel*, whereas
    evaluating that kernel at one point forgets the subprobability structure
    and exposes only a measure.  We therefore use a kernel from a fixed
    discrete root carrier as the actual higher-kinded backend.  All kernels
    built by this module are observationally read at [MCBottom]. *)
Definition MathCompKernelMeasure (A : Type) : Type :=
  R.-spker (mc_carrier unit) ~> (mc_carrier A).

Definition mathcomp_kernel_root {A}
    (mu : MathCompKernelMeasure A) :
    measure (mc_carrier A) R :=
  mu (MCBottom : mc_carrier unit).

Lemma mathcomp_kernel_root_le1 {A} (mu : MathCompKernelMeasure A) :
  mathcomp_kernel_root mu [set: mc_carrier A] <= 1.
Proof. exact: sprob_kernel_le1. Qed.

Definition mathcomp_kernel_root_fun {A} (mu : MathCompKernelMeasure A) :=
  fun U : set (mc_carrier A) => mathcomp_kernel_root mu U.

Lemma mathcomp_kernel_root_fun0 {A} (mu : MathCompKernelMeasure A) :
  mathcomp_kernel_root_fun mu set0 = 0.
Proof. exact: measure0. Qed.

Lemma mathcomp_kernel_root_fun_ge0 {A} (mu : MathCompKernelMeasure A) U :
  0 <= mathcomp_kernel_root_fun mu U.
Proof. exact: measure_ge0. Qed.

Lemma mathcomp_kernel_root_fun_sigma_additive {A}
    (mu : MathCompKernelMeasure A) :
  semi_sigma_additive (mathcomp_kernel_root_fun mu).
Proof. exact: measure_semi_sigma_additive. Qed.

HB.instance Definition mathcomp_kernel_root_fun_is_measure {A}
    (mu : MathCompKernelMeasure A) :=
  @measure.isMeasure.Build _ (mc_carrier A) R (mathcomp_kernel_root_fun mu)
    (@mathcomp_kernel_root_fun0 A mu)
    (@mathcomp_kernel_root_fun_ge0 A mu)
    (@mathcomp_kernel_root_fun_sigma_additive A mu).

HB.instance Definition mathcomp_kernel_root_is_subprobability {A}
    (mu : MathCompKernelMeasure A) :=
  @Measure_isSubProbability.Build _ _ R (mathcomp_kernel_root_fun mu)
    (@mathcomp_kernel_root_le1 A mu).

Definition mathcomp_kernel_root_subprobability {A}
    (mu : MathCompKernelMeasure A) :
  subprobability (mc_carrier A) R :=
  [the subprobability (mc_carrier A) R of
    mathcomp_kernel_root_fun mu].

Definition mathcomp_diagonal_fun {A}
    (mu : MathCompKernelMeasure A) :=
  pushforward (mathcomp_kernel_root_subprobability mu)
    (mc_joint_diagonal A).

Lemma mathcomp_diagonal_fun0 {A} (mu : MathCompKernelMeasure A) :
  mathcomp_diagonal_fun mu set0 = 0.
Proof. by rewrite /mathcomp_diagonal_fun /pushforward preimage_set0 measure0. Qed.

Lemma mathcomp_diagonal_fun_ge0 {A} (mu : MathCompKernelMeasure A) U :
  0 <= mathcomp_diagonal_fun mu U.
Proof. exact: measure_ge0. Qed.

Lemma mathcomp_diagonal_fun_sigma_additive {A}
    (mu : MathCompKernelMeasure A) :
  semi_sigma_additive (mathcomp_diagonal_fun mu).
Proof.
  move=> F mF tF mUF; rewrite /mathcomp_diagonal_fun /pushforward
    preimage_bigcup.
  apply: measure_semi_sigma_additive.
  - by move=> n.
  - apply/trivIsetP=> /= i j _ _ ij; rewrite -preimage_setI.
    have Hij : F i `&` F j = set0.
    { move/trivIsetP: tF=> H. exact: H i j Logic.I Logic.I ij. }
    by rewrite Hij preimage_set0.
  - by [].
Qed.

HB.instance Definition mathcomp_diagonal_fun_is_measure {A}
    (mu : MathCompKernelMeasure A) :=
  @measure.isMeasure.Build _ (mc_joint A A) R
    (mathcomp_diagonal_fun mu)
    (@mathcomp_diagonal_fun0 A mu)
    (@mathcomp_diagonal_fun_ge0 A mu)
    (@mathcomp_diagonal_fun_sigma_additive A mu).

Lemma mathcomp_diagonal_fun_le1 {A} (mu : MathCompKernelMeasure A) :
  mathcomp_diagonal_fun mu [set: mc_joint A A] <= 1.
Proof.
  change (mathcomp_kernel_root mu [set: mc_carrier A] <= 1).
  exact: mathcomp_kernel_root_le1.
Qed.

HB.instance Definition mathcomp_diagonal_fun_is_subprobability {A}
    (mu : MathCompKernelMeasure A) :=
  @Measure_isSubProbability.Build _ _ R (mathcomp_diagonal_fun mu)
    (@mathcomp_diagonal_fun_le1 A mu).

Definition mathcomp_diagonal_joint {A}
    (mu : MathCompKernelMeasure A) : subprobability (mc_joint A A) R :=
  [the subprobability (mc_joint A A) R of mathcomp_diagonal_fun mu].

Definition mathcomp_kernel_ret {A} (x : A) :
    MathCompKernelMeasure A :=
  mathcomp_source_kernel (mathcomp_measure_ret x).

(** Embed a Boolean value into the returned-value part of the carrier. *)
Definition mc_bool_value (x : bool) : mc_carrier bool := MCValue x.

Lemma measurable_mc_bool_value :
  measurable_fun [set: bool] mc_bool_value.
Proof. by []. Qed.

HB.instance Definition mc_bool_value_is_measurable :=
  @isMeasurableFun.Build _ _ bool (mc_carrier bool) mc_bool_value
    measurable_mc_bool_value.

(** A genuine real-valued Bernoulli law, transported into the carrier.  In
    contrast with finite rational [Enum], this representation is closed
    under irrational parameters. *)
Definition mathcomp_bernoulli_probability (q : R) :
    probability (mc_carrier bool) R :=
  [the probability (mc_carrier bool) R of
    distribution (bernoulli q) [mfun of mc_bool_value]].

Definition mathcomp_bernoulli_measure (q : R) :
  subprobability (mc_carrier bool) R :=
  [the subprobability (mc_carrier bool) R of
    (mathcomp_bernoulli_probability q :
      measure (mc_carrier bool) R)].

Definition mathcomp_bernoulli (q : R) :
    MathCompKernelMeasure bool :=
  mathcomp_source_kernel (mathcomp_bernoulli_measure q).

Lemma mathcomp_bernoulli_true_mass (q : R) (q01 : (0 <= q <= 1)%R) :
  mathcomp_kernel_root (mathcomp_bernoulli q) [set MCValue true] = q%:E.
Proof.
  rewrite /mathcomp_kernel_root /mathcomp_bernoulli
    /mathcomp_source_kernel /mathcomp_source_measure
    /mathcomp_bernoulli_measure /mathcomp_bernoulli_probability
    /distribution /pushforward /=.
  have -> : mc_bool_value @^-1` [set MCValue true] = [set true].
  { apply/seteqP; split=> b /=; by case: b. }
  rewrite /bernoulli q01 fsbig_set1 /bernoulli_pmf.
  reflexivity.
Qed.

Lemma mathcomp_bernoulli_false_mass (q : R) (q01 : (0 <= q <= 1)%R) :
  mathcomp_kernel_root (mathcomp_bernoulli q) [set MCValue false] =
    (1 - q)%:E.
Proof.
  rewrite /mathcomp_kernel_root /mathcomp_bernoulli
    /mathcomp_source_kernel /mathcomp_source_measure
    /mathcomp_bernoulli_measure /mathcomp_bernoulli_probability
    /distribution /pushforward /=.
  have -> : mc_bool_value @^-1` [set MCValue false] = [set false].
  { apply/seteqP; split=> b /=; by case: b. }
  rewrite /bernoulli q01 fsbig_set1 /bernoulli_pmf.
  reflexivity.
Qed.

Lemma mathcomp_bernoulli_bottom_mass (q : R) :
  mathcomp_kernel_root (mathcomp_bernoulli q) [set MCBottom] = 0.
Proof.
  rewrite /mathcomp_kernel_root /mathcomp_bernoulli
    /mathcomp_source_kernel /mathcomp_source_measure
    /mathcomp_bernoulli_measure /mathcomp_bernoulli_probability
    /distribution /pushforward /=.
  have -> : mc_bool_value @^-1` [set MCBottom] = set0.
  { apply/seteqP; split=> b /=; by case: b. }
  exact: measure0.
Qed.

Definition mathcomp_kernel_extend_measure {A B}
    (k : A -> MathCompKernelMeasure B)
    (x : mc_carrier A) : measure (mc_carrier B) R :=
  match x with
  | MCBottom => mathcomp_bottom_measure
  | MCValue a => mathcomp_kernel_root (k a)
  end.

Lemma measurable_mathcomp_kernel_extend {A B}
    (k : A -> MathCompKernelMeasure B) U :
  measurable U -> measurable_fun [set: mc_carrier A]
    (fun x => mathcomp_kernel_extend_measure k x U).
Proof. move=> mU mtop Y mY. by []. Qed.

HB.instance Definition mathcomp_kernel_extend_is_kernel {A B}
    (k : A -> MathCompKernelMeasure B) :=
  @isKernel.Build _ _ (mc_carrier A) (mc_carrier B) R
    (mathcomp_kernel_extend_measure k)
    (measurable_mathcomp_kernel_extend k).

Lemma mathcomp_kernel_extend_subprobability {A B}
    (k : A -> MathCompKernelMeasure B) :
  ereal_sup [set mathcomp_kernel_extend_measure k x [set: mc_carrier B]
    | x in [set: mc_carrier A]] <= 1.
Proof.
  apply/(sprob_kernelP (mathcomp_kernel_extend_measure k)).
  move=> [|a].
  - exact: sprobability_setT.
  - exact: sprob_kernel_le1.
Qed.

HB.instance Definition mathcomp_kernel_extend_is_subprobability_kernel {A B}
    (k : A -> MathCompKernelMeasure B) :=
  Kernel_isSubProbability.Build _ _ _ _ R
    (mathcomp_kernel_extend_measure k)
    (mathcomp_kernel_extend_subprobability k).

Definition mathcomp_kernel_extend {A B}
    (k : A -> MathCompKernelMeasure B) :
    R.-spker (mc_carrier A) ~> (mc_carrier B) :=
  [the R.-spker (mc_carrier A) ~> (mc_carrier B) of
    mathcomp_kernel_extend_measure k].

Definition mathcomp_kernel_bind {A B}
    (mu : MathCompKernelMeasure A)
    (k : A -> MathCompKernelMeasure B) :
    MathCompKernelMeasure B :=
  [the R.-spker (mc_carrier unit) ~> (mc_carrier B) of
    mkcomp_noparam mu (mathcomp_kernel_extend k)].

Definition mathcomp_kernel_eq {A}
    (mu nu : MathCompKernelMeasure A) : Prop :=
  forall U : set (mc_carrier A), measurable U -> ~ U MCBottom ->
    mathcomp_kernel_root mu U = mathcomp_kernel_root nu U.

Definition mathcomp_kernel_ae {A}
    (mu : MathCompKernelMeasure A) (P : A -> Prop) : Prop :=
  mathcomp_measure_ae (mathcomp_kernel_root mu) P.

Definition mathcomp_kernel_lift {A B} (rel : A -> B -> Prop)
    (mu : MathCompKernelMeasure A)
    (nu : MathCompKernelMeasure B) : Prop :=
  mathcomp_measure_lift rel
    (mathcomp_kernel_root mu) (mathcomp_kernel_root nu).

Lemma mathcomp_diagonal_left {A} (mu : MathCompKernelMeasure A)
    (U : set (mc_carrier A)) :
  mathcomp_diagonal_joint mu (mc_joint_fst @^-1` U) =
    mathcomp_kernel_root mu U.
Proof.
  change (mathcomp_kernel_root mu
    ((mc_joint_diagonal A) @^-1` (mc_joint_fst @^-1` U)) =
    mathcomp_kernel_root mu U).
  congr (mathcomp_kernel_root mu _).
Qed.

Lemma mathcomp_diagonal_right {A} (mu : MathCompKernelMeasure A)
    (U : set (mc_carrier A)) :
  mathcomp_diagonal_joint mu (mc_joint_snd @^-1` U) =
    mathcomp_kernel_root mu U.
Proof.
  change (mathcomp_kernel_root mu
    ((mc_joint_diagonal A) @^-1` (mc_joint_snd @^-1` U)) =
    mathcomp_kernel_root mu U).
  congr (mathcomp_kernel_root mu _).
Qed.

Lemma mathcomp_diagonal_related {A} (rel : A -> A -> Prop)
    (mu : MathCompKernelMeasure A) :
  Reflexive rel ->
  almost_everywhere (mathcomp_diagonal_joint mu) (mc_relation rel).
Proof.
  move=> Hrel. rewrite /almost_everywhere.
  apply/negligibleP; first by [].
  change (mathcomp_kernel_root mu
    ((mc_joint_diagonal A) @^-1` (~` mc_relation rel)) = 0).
  have -> : (mc_joint_diagonal A) @^-1` (~` mc_relation rel) = set0.
  { apply/seteqP; split=> x H.
    - destruct x as [|a]; first exact: H Logic.I.
      exact: H (Hrel a).
    - exact: False_rect _ H. }
  exact: measure0.
Qed.

Lemma mathcomp_kernel_lift_refl {A} (rel : A -> A -> Prop)
    (mu : MathCompKernelMeasure A) :
  Reflexive rel -> mathcomp_kernel_lift rel mu mu.
Proof.
  move=> Hrel. exists (mathcomp_diagonal_joint mu).
  split.
  - move=> U _ _. exact: mathcomp_diagonal_left.
  - split.
    + move=> U _ _. exact: mathcomp_diagonal_right.
    + exact: mathcomp_diagonal_related Hrel.
Qed.

Definition mathcomp_ret_joint {A B} (x : A) (y : B) :
    subprobability (mc_joint A B) R :=
  [the subprobability (mc_joint A B) R of
    dirac (MCJoint (MCValue x) (MCValue y))].

Lemma mathcomp_kernel_lift_ret {A B} (rel : A -> B -> Prop) x y :
  rel x y ->
  mathcomp_kernel_lift rel (mathcomp_kernel_ret x) (mathcomp_kernel_ret y).
Proof.
  move=> Hxy. exists (mathcomp_ret_joint x y).
  constructor.
  - move=> U mU _.
    rewrite /mathcomp_ret_joint /mathcomp_kernel_root /mathcomp_kernel_ret
      /mathcomp_source_kernel /mathcomp_source_measure
      /mathcomp_measure_ret /dirac /=.
    reflexivity.
  - constructor.
    + move=> V mV _.
      rewrite /mathcomp_ret_joint /mathcomp_kernel_root /mathcomp_kernel_ret
        /mathcomp_source_kernel /mathcomp_source_measure
        /mathcomp_measure_ret /dirac /=.
      reflexivity.
    + rewrite /almost_everywhere. apply/negligibleP; first by [].
      change (((\1_(~` mc_relation rel)
        (MCJoint (MCValue x) (MCValue y))) : R)%:E = 0).
      rewrite indicE.
      have Hnot : MCJoint (MCValue x) (MCValue y) \notin
          (~` mc_relation rel).
      { rewrite notin_setE /= /mc_relation.
        have Hnn : ~ ~ rel x y := fun Hn => Hn Hxy.
        exact Hnn. }
      by rewrite (negbTE Hnot).
Qed.

#[global] Instance MathCompKernelMeasureInterface :
    MeasureInterface MathCompKernelMeasure := {
  meas_ret := @mathcomp_kernel_ret;
  meas_bind := @mathcomp_kernel_bind;
  meas_eq := @mathcomp_kernel_eq;
  meas_ae := @mathcomp_kernel_ae;
  meas_lift := @mathcomp_kernel_lift
}.

#[global] Instance MathCompKernelMeasureCoreLaws :
    @MeasureCoreLaws MathCompKernelMeasure
      MathCompKernelMeasureInterface.
Proof.
  constructor.
  - move=> A mu P Q HPQ Hae.
    rewrite /almost_everywhere in Hae *.
    eapply negligibleS; [|exact Hae].
    move=> [|a] /= HnQ HP; apply: HnQ.
    - exact: HP.
    - exact: HPQ HP.
  - move=> A B rel rel' mu nu Hmono.
    move=> [joint [Hleft [Hright Hae]]].
    exists joint. repeat split=> //.
    rewrite /almost_everywhere in Hae *.
    eapply negligibleS; [|exact Hae].
    move=> [x y] Hnot' Hrel; apply: Hnot'.
    rewrite /mc_relation in Hrel *.
    destruct x as [|a], y as [|b]; simpl in Hrel |- *; auto.
  - move=> A rel mu Hrel.
    exact: mathcomp_kernel_lift_refl Hrel.
  - move=> A B rel x y Hxy.
    exact: mathcomp_kernel_lift_ret Hxy.
Qed.

Lemma mathcomp_kernel_eq_refl A :
  Reflexive (@mathcomp_kernel_eq A).
Proof. by move=> mu U mU nbot. Qed.

Lemma mathcomp_kernel_eq_sym A :
  Symmetric (@mathcomp_kernel_eq A).
Proof. by move=> mu nu H U mU nbot; rewrite H. Qed.

Lemma mathcomp_kernel_eq_trans A :
  Transitive (@mathcomp_kernel_eq A).
Proof. by move=> mu nu xi Hmn Hnx U mU nbot; rewrite Hmn // Hnx. Qed.

Lemma mathcomp_kernel_ae_true {A} (mu : MathCompKernelMeasure A) :
  mathcomp_kernel_ae mu (fun _ => True).
Proof. apply: aeW=> [[|a]]; exact I. Qed.

Lemma mathcomp_kernel_ae_conj {A} (mu : MathCompKernelMeasure A)
    (P Q : A -> Prop) :
  mathcomp_kernel_ae mu P -> mathcomp_kernel_ae mu Q ->
  mathcomp_kernel_ae mu (fun x => P x /\ Q x).
Proof.
  rewrite /mathcomp_kernel_ae /mathcomp_measure_ae /almost_everywhere.
  move=> HP HQ.
  eapply negligibleS; [|exact (negligibleU HP HQ)].
  move=> [|a] /= Hnot; [case Hnot; exact I|].
  case: (pselect (P a)) => HPa.
  - right. move=> HQa. exact: Hnot (conj HPa HQa).
  - by left.
Qed.

Lemma mathcomp_kernel_lift_proper_l {A B} (rel : A -> B -> Prop)
    (mu mu' : MathCompKernelMeasure A) (nu : MathCompKernelMeasure B) :
  mathcomp_kernel_eq mu mu' ->
  mathcomp_kernel_lift rel mu nu ->
  mathcomp_kernel_lift rel mu' nu.
Proof.
  move=> Hmm [joint [Hleft [Hright Hrel]]].
  exists joint. repeat split=> //.
  move=> U mU nbot. rewrite -Hmm //.
  exact: Hleft.
Qed.

Lemma mathcomp_kernel_lift_proper_r {A B} (rel : A -> B -> Prop)
    (mu : MathCompKernelMeasure A) (nu nu' : MathCompKernelMeasure B) :
  mathcomp_kernel_eq nu nu' ->
  mathcomp_kernel_lift rel mu nu ->
  mathcomp_kernel_lift rel mu nu'.
Proof.
  move=> Hnn [joint [Hleft [Hright Hrel]]].
  exists joint. repeat split=> //.
  move=> U mU nbot. rewrite -Hnn //.
  exact: Hright.
Qed.

(** ** Omega limits and termination mass

    The finite approximants used by [meas_iter] form increasing chains in
    the intended applications.  Their limit is characterized setwise on
    returned-value events: their mass is the supremum along the chain.
    Events containing [MCBottom] are deliberately excluded because the
    unfinished mass decreases as fuel grows.  Keeping this relation in the
    abstract interface avoids choosing a representation of limits at the
    [ptree] level. *)
Definition mathcomp_kernel_zero {A} : MathCompKernelMeasure A :=
  mathcomp_source_kernel mathcomp_bottom_measure.

Definition mathcomp_kernel_lub {A}
    (chain : nat -> MathCompKernelMeasure A)
    (mu : MathCompKernelMeasure A) : Prop :=
  forall U : set (mc_carrier A), measurable U -> ~ U MCBottom ->
    mathcomp_kernel_root mu U =
      ereal_sup [set mathcomp_kernel_root (chain n) U | n in [set: nat]].

Definition mc_returned {A} : set (mc_carrier A) :=
  [set x | match x with MCBottom => False | MCValue _ => True end].

Definition mathcomp_kernel_total {A}
    (mu : MathCompKernelMeasure A) : Prop :=
  mathcomp_kernel_root mu (@mc_returned A) = 1.

Lemma mathcomp_bernoulli_total (q : R) :
  mathcomp_kernel_total (mathcomp_bernoulli q).
Proof.
  rewrite /mathcomp_kernel_total /mathcomp_kernel_root
    /mathcomp_bernoulli /mathcomp_source_kernel /mathcomp_source_measure
    /mathcomp_bernoulli_measure /mathcomp_bernoulli_probability
    /distribution /pushforward /=.
  have -> : mc_bool_value @^-1` (@mc_returned bool) = [set: bool].
  { apply/seteqP; split=> b //=. }
  exact: probability_setT.
Qed.

#[global] Instance MathCompKernelMeasureOmegaInterface :
    @MeasureOmegaInterface MathCompKernelMeasure
      MathCompKernelMeasureInterface := {
  meas_zero := @mathcomp_kernel_zero;
  meas_lub := @mathcomp_kernel_lub;
  meas_total := @mathcomp_kernel_total
}.

Lemma mathcomp_kernel_lub_unique {A}
    (chain : nat -> MathCompKernelMeasure A) mu nu :
  mathcomp_kernel_lub chain mu ->
  mathcomp_kernel_lub chain nu ->
  mathcomp_kernel_eq mu nu.
Proof.
  move=> Hmu Hnu U mU nbot. rewrite Hmu // Hnu //.
Qed.

Lemma mathcomp_kernel_lub_proper {A}
    (c1 c2 : nat -> MathCompKernelMeasure A) mu :
  (forall n, mathcomp_kernel_eq (c1 n) (c2 n)) ->
  mathcomp_kernel_lub c1 mu ->
  mathcomp_kernel_lub c2 mu.
Proof.
  move=> Hc Hlim U mU nbot. rewrite Hlim //.
  congr (ereal_sup _). apply/seteqP; split=> x.
  - move=> [n _ <-].
    exists n; first by [].
    by rewrite (Hc n U mU nbot).
  - move=> [n _ <-].
    exists n; first by [].
    by rewrite (Hc n U mU nbot).
Qed.

#[global] Instance MathCompKernelMeasureOmegaLaws :
    @MeasureOmegaLaws MathCompKernelMeasure
      MathCompKernelMeasureInterface MathCompKernelMeasureOmegaInterface := {
  meas_lub_unique := @mathcomp_kernel_lub_unique;
  meas_lub_proper := @mathcomp_kernel_lub_proper
}.

End BackendShape.
