(** A successful checked input uses the existing forward semantics. The
    compile premise is the frontend entry condition; the semantic result
    already holds for every well-typed [pgcl] command. This wrapper neither
    specifies the textual parser nor proves preservation of an independent
    source semantics. Execution still follows [run], including State interp. *)
From Coq Require Import Utf8.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.FreeOmega Require Import Measure.
From PTree.Eq Require Import PTreeKernel.
From PTree.Interp Require Import ReturnIteration.
From PTree.Examples.PGCL Require Import Syntax Interpretation Forward.
From PTree.Examples.PGCL.Backend Require Import Finite.
From PTree.Examples.PGCL.Runtime Require Import Frontend.

Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).

Theorem compile_hitting (src : source) (c : pgcl) (s : store) :
  compile src = Some c →
  ptree_stable_hitting (FI := FI) (FO := FO)
    (observe (run (E := void1) rational_coin c s))
    (iteration_return_map (E := void1) (MN := SubEnumQ)
      (denote (FI := FI) (FO := FO) rational_coin c s)).
Proof. intros _. apply rational_pgcl_hitting. Qed.
