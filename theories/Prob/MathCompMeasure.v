Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets functions cardinality reals.
From mathcomp.analysis Require Import measure probability kernel
  measurable_realfun ereal.

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
    set (mc_carrier A * mc_carrier B) :=
  [set xy | match xy with
   | (MCBottom, MCBottom) => True
   | (MCValue a, MCValue b) => rel a b
   | _ => False
   end].

Definition mathcomp_coupling {A B} (rel : A -> B -> Prop)
    (mu : measure (mc_carrier A) R)
    (nu : measure (mc_carrier B) R) : Prop :=
  exists joint : subprobability (mc_carrier A * mc_carrier B)%type R,
    (forall U : set (mc_carrier A), measurable U ->
      joint (fst @^-1` U) = mu U) /\
    (forall V : set (mc_carrier B), measurable V ->
      joint (snd @^-1` V) = nu V) /\
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

Definition mathcomp_kernel_ret {A} (x : A) :
    MathCompKernelMeasure A :=
  mathcomp_source_kernel (mathcomp_measure_ret x).

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

#[global] Instance MathCompKernelMeasureInterface :
    MeasureInterface MathCompKernelMeasure := {
  meas_ret := @mathcomp_kernel_ret;
  meas_bind := @mathcomp_kernel_bind;
  meas_eq := @mathcomp_kernel_eq;
  meas_ae := @mathcomp_kernel_ae;
  meas_lift := @mathcomp_kernel_lift
}.

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
