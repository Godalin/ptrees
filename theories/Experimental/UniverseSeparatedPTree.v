Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From mathcomp Require Import ssralg ssrnum reals.
From PTree.Prob Require Import MathCompMeasure.

Import GRing.Theory.
#[local] Open Scope ring_scope.

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
