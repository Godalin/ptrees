Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype choice ssralg ssrnum reals boolp classical_sets
  numfun lebesgue_integral.
From mathcomp.analysis Require Import measure probability kernel
  measurable_realfun ereal.
From PTree.Prob Require Import MathCompMeasure.

Import GRing.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope classical_set_scope.
#[local] Open Scope ereal_scope.

(** A universe-separated probe for the next PTree representation.  The
    sampled carrier universe and the universe containing a measure value are
    deliberately independent.  The current [PTreeDefinitionNew] implicitly
    identifies them when frontiers contain recursive trees, which prevents
    MathComp measurable kernels from inhabiting the generic weak theory. *)
Polymorphic Section UniverseSeparatedPTree.

Universe sample measure event result tree.

Context (E : Type@{sample} -> Type@{event}).
Context (M : Type@{sample} -> Type@{measure}).
Context (R : Type@{result}).

Variant uptreeF (T : Type@{tree}) : Type :=
  | URetF (r : R)
  | UTauF (t : T)
  | UVisF {X : Type@{sample}} (e : E X) (k : X -> T)
  | UProbF {X : Type@{sample}} (mu : M X) (k : X -> T).

CoInductive uptree : Type :=
  | ugo : uptreeF uptree -> uptree.

End UniverseSeparatedPTree.

Arguments uptree _ _ _ : clear implicits.

Unset Universe Polymorphism.

(** The intended backend typechecks at this separated signature.  This
    definition is a compile-time regression test for the migration design. *)
Definition mathcomp_uptree (R : realType) (A : Type) : Type :=
  uptree (fun _ => Empty_set) (MathCompKernelMeasure R) A.

Definition mathcomp_uptree_direct_bool (R : realType) :
    mathcomp_uptree R bool :=
  @ugo (fun _ => Empty_set) (MathCompKernelMeasure R) bool
    (@UProbF (fun _ => Empty_set) (MathCompKernelMeasure R) bool _ bool
      (@mathcomp_bernoulli R (1 / 2))
      (fun b => @ugo (fun _ => Empty_set) (MathCompKernelMeasure R) bool
        (@URetF (fun _ => Empty_set) (MathCompKernelMeasure R) bool _ b))).

(** The next obstruction is not the probability node itself, but applying the
    *same fixed* higher-kinded [M] to a frontier head containing a recursive
    tree.  The recursive tree necessarily lives above [M]'s sample universe.
    Keeping this rejected definition as a checked [Fail] command makes the
    architectural boundary executable rather than merely documentary. *)
Polymorphic Section SameMeasureFrontierBoundary.

Universe sample measure event result tree.

Context (E : Type@{sample} -> Type@{event}).
Context (M : Type@{sample} -> Type@{measure}).
Context (R : Type@{result}).

Variant ufrontier_head : Type :=
  | UFHRet (r : R)
  | UFHVis {X : Type@{sample}} (e : E X)
      (k : X -> uptree E M R).

Fail Definition same_measure_frontier : Type := M ufrontier_head.

End SameMeasureFrontierBoundary.

(** A two-level signature removes that cycle: [MN] interprets source-level
    probability nodes, while [MF] interprets semantic frontier carriers.
    A future migration must additionally connect them with a promotion/bind
    law; universe separation alone is the representational prerequisite. *)
Polymorphic Section TwoLevelFrontierProbe.

Universe sample node_measure event result frontier_sample frontier_measure.

Context (E : Type@{sample} -> Type@{event}).
Context (MN : Type@{sample} -> Type@{node_measure}).
Context (MF : Type@{frontier_sample} -> Type@{frontier_measure}).
Context (R : Type@{result}).

Variant two_level_head : Type :=
  | TLHRet (r : R)
  | TLHVis {X : Type@{sample}} (e : E X)
      (k : X -> uptree E MN R).

Definition two_level_frontier : Type := MF two_level_head.

End TwoLevelFrontierProbe.

Arguments two_level_frontier _ _ _ _ : clear implicits.

(** The mixed operation actually required by [APFProb]: integrate a
    frontier-valued kernel against a source-level node measure.  It is more
    precise than an unexplained coercion from [MN] to [MF], and states the
    semantic bridge the two-level representation must provide. *)
Polymorphic Class TwoLevelMeasureInterface@{sample node_measure
    frontier_sample frontier_measure}
    (MN : Type@{sample} -> Type@{node_measure})
    (MF : Type@{frontier_sample} -> Type@{frontier_measure}) := {
  frontier_ret : forall {A : Type@{frontier_sample}}, A -> MF A;
  frontier_bind_node : forall {A : Type@{sample}}
      {B : Type@{frontier_sample}}, MN A -> (A -> MF B) -> MF B
}.

(** The abstract two-level shape typechecks, but today's
    [MathCompKernelMeasure] is a monomorphic universe constant: it cannot yet
    be instantiated independently at both levels.  Thus the migration also
    requires a universe-polymorphic backend (or two separately generated
    backend layers), in addition to the mixed bind law above. *)
Fail Definition mathcomp_two_level_frontier (R : realType) (A : Type) : Type :=
  @two_level_frontier (fun _ => Empty_set)
    (MathCompKernelMeasure R) (MathCompKernelMeasure R) A.

(** With the MathComp measurable hierarchy imported explicitly, the kernel
    type synonym itself can be redeclared polymorphically, so the abstract
    two-level *shape* inhabits both levels.  This does not make the already
    sealed kernel operations or their HB instances polymorphic. *)
Polymorphic Definition PolyMathCompKernelMeasure (R : realType)
    (A : Type) : Type :=
  R.-spker (mc_carrier unit) ~> (mc_carrier A).

Polymorphic Definition poly_mathcomp_two_level_frontier
    (R : realType) (A : Type) : Type :=
  @two_level_frontier (fun _ => Empty_set)
    (PolyMathCompKernelMeasure R) (PolyMathCompKernelMeasure R) A.

(** At its sealed universe levels, the existing bind operation has the right
    mixed source/target type and instantiates the abstract interface. *)
Definition mathcomp_mixed_bind {R : realType} {A B : Type}
    (mu : MathCompKernelMeasure R A)
    (k : A -> PolyMathCompKernelMeasure R B) :
    PolyMathCompKernelMeasure R B :=
  @mathcomp_kernel_bind R A B mu k.

Definition mathcomp_mixed_ret {R : realType} {A : Type} (x : A) :
    PolyMathCompKernelMeasure R A :=
  @mathcomp_kernel_ret R A x.

Definition MathCompTwoLevelMeasureInterface (R : realType) :
    TwoLevelMeasureInterface
      (MathCompKernelMeasure R) (PolyMathCompKernelMeasure R) :=
  {| frontier_ret := @mathcomp_mixed_ret R;
     frontier_bind_node := @mathcomp_mixed_bind R |}.

(** The decisive negative regression: that sealed target universe remains
    below the recursive tree, so it still cannot integrate a genuine real
    Bernoulli node into a recursive frontier carrier.  A working migration
    must generate the HB instance and mixed operation in the same explicit
    high-universe section as the frontier head. *)
Fail Polymorphic Definition mathcomp_bernoulli_bool_frontier (R : realType) :
    @PolyMathCompKernelMeasure R
      (two_level_head (fun _ => Empty_set)
        (MathCompKernelMeasure R) bool) :=
  mathcomp_mixed_bind (@mathcomp_bernoulli R (1 / 2))
    (fun b => mathcomp_mixed_ret (@TLHRet (fun _ => Empty_set)
      (MathCompKernelMeasure R) bool b)).
