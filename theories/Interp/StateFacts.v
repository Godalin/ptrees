(** Backend-independent structural State algebra. This does NOT claim that
    arbitrary source peutt is preserved by eliminating handlers: that needs
    the separate collapsed-event argument. Structural equations already
    justify stateful program rewrites without any probability axioms. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
From Coq.Program Require Import Equality.
From Coinduction Require Import all.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import PStruct Shallow.
From PTree.Interp Require Import State.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Notation "` R" := (elem R) (at level 10).

Section StateFacts.
Context {S : Type} {E MN : Type -> Type}.

Lemma run_state_ret {A} (a : A) s :
  pstruct eq (@run_state S E MN A (Ret a) s) (Ret (s, a)).
Proof. apply observe_eq_pstruct. reflexivity. Qed.

Lemma run_state_tau {A} (t : ptree (stateE S +' E) MN A) s :
  pstruct eq (run_state (Tau t) s) (Tau (run_state t s)).
Proof. apply observe_eq_pstruct. reflexivity. Qed.

Lemma run_state_prob {A X} (mu : MN X)
    (k : X -> ptree (stateE S +' E) MN A) s :
  pstruct eq (run_state (Prob mu k) s) (Prob mu (fun x => run_state (k x) s)).
Proof. apply observe_eq_pstruct. reflexivity. Qed.

Lemma run_state_get {A} (k : S -> ptree (stateE S +' E) MN A) s :
  pstruct eq (run_state (Vis (inl1 (Get S)) k) s) (Tau (run_state (k s) s)).
Proof. apply observe_eq_pstruct. reflexivity. Qed.

Lemma run_state_put {A} (k : unit -> ptree (stateE S +' E) MN A) s s' :
  pstruct eq (run_state (Vis (inl1 (Put S s')) k) s) (Tau (run_state (k tt) s')).
Proof. apply observe_eq_pstruct. reflexivity. Qed.

Lemma run_state_forward {A X} (e : E X)
    (k : X -> ptree (stateE S +' E) MN A) s :
  pstruct eq (run_state (Vis (inr1 e) k) s) (Vis e (fun x => run_state (k x) s)).
Proof. apply observe_eq_pstruct. reflexivity. Qed.

Definition state_pstruct_candidate {A B} (RR : A -> B -> Prop)
    (v : ptree E MN (S * A)) (w : ptree E MN (S * B)) : Prop :=
  exists t u s, v = run_state t s /\ w = run_state u s /\ pstruct RR t u.

Theorem run_state_pstruct {A B} (RR : A -> B -> Prop)
    (t : ptree (stateE S +' E) MN A) (u : ptree (stateE S +' E) MN B) s :
  pstruct RR t u -> pstruct (state_result_rel RR) (run_state t s) (run_state u s).
Proof.
  intro Htu.
  assert (Hmain : forall (v : ptree E MN (S * A)) (w : ptree E MN (S * B)),
    state_pstruct_candidate RR v w ->
    pstruct (state_result_rel RR) v w).
  { unfold pstruct. coinduction CH CIH.
    intros v w [t0 [u0 [s0 [-> [-> Hs]]]]]. unfold pstruct_body.
    change (pstructF (state_result_rel RR) (` CH)
      (observe (run_state t0 s0)) (observe (run_state u0 s0))).
    rewrite !observe_run_state.
    pose proof (pstruct_unfold Hs) as Hstep. dependent destruction Hstep;
      rewrite <- x0, <- x; cbn.
    - constructor. split; [reflexivity|exact H].
    - constructor. apply CIH. eexists _, _, _. repeat split; eauto.
    - destruct e as [se|fe].
      + destruct (state_response se s0) as [s' y]. constructor. apply CIH.
        eexists _, _, _. repeat split; eauto.
      + constructor. intro y. apply CIH. eexists _, _, _. repeat split; eauto.
    - constructor. intro y. apply CIH. eexists _, _, _. repeat split; eauto. }
  apply Hmain. exists t, u, s. repeat split; auto.
Qed.

Definition state_bind_candidate {A B} (k : A -> ptree (stateE S +' E) MN B)
    (v w : ptree E MN (S * B)) : Prop :=
  (exists t s, v = run_state (PTree.bind t k) s /\
    w = PTree.bind (run_state t s) (fun sa => run_state (k (snd sa)) (fst sa))) \/
    pstruct eq v w.

Theorem run_state_bind {A B} (t : ptree (stateE S +' E) MN A)
    (k : A -> ptree (stateE S +' E) MN B) s :
  pstruct eq (run_state (PTree.bind t k) s)
    (PTree.bind (run_state t s) (fun sa => run_state (k (snd sa)) (fst sa))).
Proof.
  assert (Hmain : forall (v w : ptree E MN (S * B)),
    state_bind_candidate k v w -> pstruct eq v w).
  { unfold pstruct. coinduction CH CIH. intros v w [Hmain|Hdone].
    - destruct Hmain as [t0 [s0 [-> ->]]]. unfold pstruct_body.
      change (pstructF eq (` CH) (observe (run_state (PTree.bind t0 k) s0))
        (observe (PTree.bind (run_state t0 s0)
          (fun sa => run_state (k (snd sa)) (fst sa))))).
      rewrite observe_run_state, !observe_bind, observe_run_state.
      destruct (observe t0) as [a|u|X e c|X mu c]; cbn.
      + rewrite <- observe_run_state.
        eapply pstructF_monotone; [|apply pstruct_unfold; apply pstruct_refl].
        intros v' w' Hvw. apply CIH. right. exact Hvw.
      + constructor. apply CIH. left. eexists _, _. split; reflexivity.
      + destruct e as [se|fe]; cbn.
        * destruct (state_response se s0) as [s' x]. cbn.
          constructor. apply CIH. left. eexists _, _. split; reflexivity.
        * constructor. intro x. apply CIH. left. eexists _, _. split; reflexivity.
      + constructor. intro x. apply CIH. left. eexists _, _. split; reflexivity.
    - unfold pstruct_body. eapply pstructF_monotone; [|apply pstruct_unfold; exact Hdone].
      intros v' w' Hvw. apply CIH. right. exact Hvw. }
  apply Hmain. left. exists t, s. split; reflexivity.
Qed.
End StateFacts.
