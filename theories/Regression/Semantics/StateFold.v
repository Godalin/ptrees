(** A real ITree execution target; stateful native sampling and unbounded
    control flow. The source sampling algebra is never obtained from Vis. *)
Set Universe Polymorphism.
From Coq Require Import List.
From ITree.Basics Require Import Basics Monad.
From ITree.Core Require Import ITreeDefinition ITreeMonad.
From ITree.Eq Require Import Eqit.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Fold IterationLaws.
From PTree.Interp Require Import State StateFold StateFoldFacts.
From PTree.Execution Require Import ITreeFold.
Fail Check PTree.Eq.PEutt.peutt.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Set Implicit Arguments.
Unset Strict Implicit.

Section ArbitraryAlgebras.
Context {S : Type} {E MN F : Type -> Type}.
Variable handle : forall X, E X -> itree F X.
Variable sample : forall X, MN X -> itree F X.

Example state_fold_commutes {A} (t : ptree (stateE S +' E) MN A) s :
  eutt eq (fold_state handle sample t s)
    (fold handle sample (run_state t s)).
Proof. apply (fold_run_state (QT := Eq1_ITree)). apply itree_iteration_uniform. Qed.

Example sample_keeps_separate_algebra {A X} (mu : MN X) (k : X -> ptree E MN A) :
  eutt eq (fold handle sample (Prob mu k))
    (ITree.bind (@sample X mu) (fun x => fold handle sample (k x))).
Proof. apply itree_fold_prob. Qed.

Example state_get_fold {A} (k : S -> ptree (stateE S +' E) MN A) s :
  eutt eq (fold_state handle sample (Vis (inl1 (Get S)) k) s)
    (fold_state handle sample (k s) s).
Proof.
  rewrite !state_fold_commutes.
  rewrite itree_fold_unfold at 1.
  unfold fold_step at 1. rewrite observe_run_state.
  cbn [PTreeDefinition.observe PTreeDefinition._observe state_response Monad.ret Monad_itree].
  rewrite bind_ret_l. reflexivity.
Qed.
End ArbitraryAlgebras.

From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Examples Require Import StateCounter.

Section InfiniteStatefulExample.
Context {F : Type -> Type}.
Variable sample : forall X, SubEnumQ X -> itree F X.
Definition no_visible_event X (e : void1 X) : itree F X := match e with end.

Example unbounded_counter_fold_agrees s :
  eutt eq (fold_state (@no_visible_event) sample count_until_success s)
    (fold (@no_visible_event) sample (run_state count_until_success s)).
Proof. apply state_fold_commutes. Qed.
End InfiniteStatefulExample.

(** A bare MonadIter is insufficient. This deliberately nonuniform iterator
    inspects unreachable states before taking one step. No new axiom is
    declared: the negative example uses Coq's existing classical decision. *)
From Coq Require Import ClassicalDescription.

Definition option_ops : Monad option := {|
  ret := fun A x => Some x;
  bind := fun A B m k => match m with Some x => k x | None => None end
|}.

Definition nonuniform_iter : MonadIter option :=
  fun A I step i =>
    if excluded_middle_informative (forall j, exists a, step j = Some (inr a))
    then match step i with Some (inr a) => Some a | _ => None end
    else None.

Definition option_observation : Eq1 option := fun A => @eq (option A).

Lemma bare_iterator_is_not_uniform :
  ~ @iteration_uniform option option_ops nonuniform_iter option_observation.
Proof.
  intro H.
  specialize (H unit bool unit
    (fun _ => Some (inr tt))
    (fun b => if b then Some (inr tt) else None)
    (fun _ => true)).
  assert (Hs : forall i : unit,
    eq1 (Eq1 := option_observation)
      (@bind option option_ops _ _ (Some (inr tt : unit + unit))
        (fun v => @ret option option_ops _ (iteration_map (fun _ : unit => true) v)))
      (Some (inr tt : bool + unit))) by reflexivity.
  specialize (H Hs tt).
  unfold eq1, option_observation, Basics.iter, nonuniform_iter in H.
  destruct (excluded_middle_informative
    (forall _ : unit, exists a : unit, Some (inr tt : unit + unit) = Some (inr a)))
    as [Hyes|Hno].
  - destruct (excluded_middle_informative
      (forall b : bool, exists a : unit,
        (if b then Some (inr tt : bool + unit) else None) = Some (inr a)))
      as [Hbad|Hgood].
    + destruct (Hbad false) as [a Ha]. discriminate.
    + discriminate.
  - exfalso. apply Hno. intro u. exists tt. reflexivity.
Qed.
