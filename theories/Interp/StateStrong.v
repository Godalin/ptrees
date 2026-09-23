(** State elimination preserves native lockstep probabilistic couplings.
    A subsequent generic structural-to-behavioral bridge is legitimate;
    this is NOT arbitrary peutt preservation by an eliminating handler. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
From Coq.Program Require Import Equality.
From Coinduction Require Import all.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure.
From PTree.Eq Require Import PStrong.
From PTree.Interp Require Import State.
Set Implicit Arguments.
Unset Strict Implicit.
Notation "` R" := (elem R) (at level 10).

Section StateStrong.
Context {S : Type} {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}.

Definition state_pstrong_candidate {A B} (RR : A -> B -> Prop)
    (v : ptree E MN (S * A)) (w : ptree E MN (S * B)) : Prop :=
  exists t u s, v = run_state t s /\ w = run_state u s /\ pstrong RR t u.

Theorem run_state_pstrong {A B} (RR : A -> B -> Prop)
    (t : ptree (stateE S +' E) MN A) (u : ptree (stateE S +' E) MN B) s :
  pstrong RR t u -> pstrong (state_result_rel RR) (run_state t s) (run_state u s).
Proof.
  intro Htu.
  assert (Hmain : forall (v : ptree E MN (S * A)) (w : ptree E MN (S * B)),
    state_pstrong_candidate RR v w -> pstrong (state_result_rel RR) v w).
  { unfold pstrong. coinduction CH CIH.
    intros v w [t0 [u0 [s0 [-> [-> Hs]]]]]. unfold pstrong_body.
    change (pstrongF (state_result_rel RR) (` CH)
      (observe (run_state t0 s0)) (observe (run_state u0 s0))).
    rewrite !observe_run_state.
    pose proof (pstrong_unfold Hs) as Hstep. dependent destruction Hstep;
      rewrite <- x0, <- x; cbn.
    - constructor. split; [reflexivity|exact H].
    - constructor. apply CIH. eexists _, _, _. repeat split; eauto.
    - destruct e as [se|fe].
      + destruct (state_response se s0) as [s' y]. constructor. apply CIH.
        eexists _, _, _. repeat split; eauto.
      + constructor. intro y. apply CIH. eexists _, _, _. repeat split; eauto.
    - constructor. eapply sem_lift_mono; [|exact H].
      intros a b Hab. apply CIH. eexists _, _, _. repeat split; eauto. }
  apply Hmain. exists t, u, s. repeat split; auto.
Qed.
End StateStrong.
