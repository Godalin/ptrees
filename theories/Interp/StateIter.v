(** State elimination commutes with guarded iteration, including probabilistic
    and still-visible loop bodies. This is structural, not a substitute for
    preservation of arbitrary behavioral source equivalence. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
From Coinduction Require Import all.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import PStruct Shallow.
From PTree.Interp Require Import State.
Set Implicit Arguments.
Unset Strict Implicit.
Notation "` R" := (elem R) (at level 10).

Section StateIteration.
Context {S I A : Type} {E MN : Type -> Type}.
Variable step : I -> ptree (stateE S +' E) MN (I + A).

Definition state_iter_result (sa : S * (I + A)) : (S * I) + (S * A) :=
  match snd sa with
  | inl i => inl (fst sa, i)
  | inr a => inr (fst sa, a)
  end.

Definition state_iter_step (si : S * I) : ptree E MN ((S * I) + (S * A)) :=
  PTree.bind (run_state (step (snd si)) (fst si))
    (fun sa => Ret (state_iter_result sa)).

Definition state_iter_source_cont (ia : I + A) : ptree (stateE S +' E) MN A :=
  match ia with inl i => Tau (PTree.iter step i) | inr a => Ret a end.

Definition state_iter_target_cont (lr : (S * I) + (S * A)) : ptree E MN (S * A) :=
  match lr with inl si => Tau (PTree.iter state_iter_step si) | inr sa => Ret sa end.

Inductive state_iter_candidate : ptree E MN (S * A) -> ptree E MN (S * A) -> Prop :=
| StateIterMain i s : state_iter_candidate
    (run_state (PTree.iter step i) s) (PTree.iter state_iter_step (s,i))
| StateIterBody t s : state_iter_candidate
    (run_state (PTree.bind t state_iter_source_cont) s)
    (PTree.bind (PTree.bind (run_state t s) (fun sa => Ret (state_iter_result sa)))
      state_iter_target_cont).

Theorem run_state_iter i s :
  pstruct eq (run_state (PTree.iter step i) s) (PTree.iter state_iter_step (s,i)).
Proof.
  assert (Hmain : forall u v, state_iter_candidate u v -> pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Hc. inversion Hc; subst.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (run_state (PTree.iter step i0) s0))
        (observe (PTree.iter state_iter_step (s0,i0)))).
      rewrite observe_run_state.
      rewrite (observing_observe (unfold_aloop_ step i0)).
      rewrite (observing_observe (unfold_aloop_ state_iter_step (s0,i0))).
      unfold state_iter_step at 1. cbn [fst snd].
      rewrite !observe_bind, observe_run_state.
      destruct (observe (step i0)) as [lr|t'|X e k|X mu k]; cbn.
      + destruct lr as [j|a]; cbn [state_iter_result].
        * constructor. apply CIH. constructor.
        * constructor. reflexivity.
      + constructor. apply CIH. constructor.
      + destruct e as [se|fe]; cbn.
        * destruct (state_response se s0) as [s' x]. constructor. apply CIH. constructor.
        * constructor. intro x. apply CIH. constructor.
      + constructor. intro x. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (run_state (PTree.bind t state_iter_source_cont) s0))
        (observe (PTree.bind
          (PTree.bind (run_state t s0) (fun sa => Ret (state_iter_result sa)))
          state_iter_target_cont))).
      rewrite observe_run_state, !observe_bind, observe_run_state.
      destruct (observe t) as [lr|t'|X e k|X mu k]; cbn.
      + destruct lr as [j|a]; cbn [state_iter_result state_iter_source_cont state_iter_target_cont].
        * constructor. apply CIH. constructor.
        * constructor. reflexivity.
      + constructor. apply CIH. constructor.
      + destruct e as [se|fe]; cbn.
        * destruct (state_response se s0) as [s' x]. constructor. apply CIH. constructor.
        * constructor. intro x. apply CIH. constructor.
      + constructor. intro x. apply CIH. constructor. }
  apply Hmain. constructor.
Qed.
End StateIteration.
