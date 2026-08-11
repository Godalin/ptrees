Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets functions cardinality reals.
From mathcomp.analysis Require Import measure probability kernel
  measurable_realfun ereal.

From PTree.Prob Require Import FrontierLift.

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
    (mu nu : subprobability (mc_carrier A) R) : Prop :=
  forall U : set (mc_carrier A), measurable U -> mu U = nu U.

(** A predicate on returned values is lifted to the carrier by declaring
    the bookkeeping bottom point valid.  Consequently missing mass never
    falsifies an almost-everywhere assertion about returned values. *)
Definition mc_predicate {A} (P : A -> Prop) : set (mc_carrier A) :=
  [set x | match x with MCBottom => True | MCValue a => P a end].

Definition mathcomp_measure_ae {A}
    (mu : subprobability (mc_carrier A) R) (P : A -> Prop) : Prop :=
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
    (mu : subprobability (mc_carrier A) R)
    (nu : subprobability (mc_carrier B) R) : Prop :=
  exists joint : subprobability (mc_carrier A * mc_carrier B)%type R,
    (forall U : set (mc_carrier A), measurable U ->
      joint (fst @^-1` U) = mu U) /\
    (forall V : set (mc_carrier B), measurable V ->
      joint (snd @^-1` V) = nu V) /\
    almost_everywhere joint (mc_relation rel).

(** The intended [MeasureInterface] lifting is existence of a subprobability
    coupling concentrated almost everywhere on the lifted relation. *)
Definition mathcomp_measure_lift {A B} (rel : A -> B -> Prop)
    (mu : subprobability (mc_carrier A) R)
    (nu : subprobability (mc_carrier B) R) : Prop :=
  mathcomp_coupling rel mu nu.

End BackendShape.
