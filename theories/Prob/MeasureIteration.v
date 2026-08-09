Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8.

From PTree.Prob Require Import FrontierLift.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Omega-completeness is deliberately separated from the finite measure
    monad laws.  [meas_lub chain limit] says that [limit] is the increasing
    limit of [chain].  Concrete models may formulate this using measurable
    sets, integrals, or pointwise masses. *)
Class MeasureOmegaInterface (M : Type -> Type)
    `{MI : MeasureInterface M} := {
  meas_zero : forall {A}, M A;
  meas_lub : forall {A}, (nat -> M A) -> M A -> Prop
}.

(** Laws needed by the unbounded frontier development.  In particular,
    uniqueness prevents an infinite internal loop from being assigned an
    arbitrary result measure. *)
Class MeasureOmegaLaws (M : Type -> Type)
    `{MI : MeasureInterface M}
    `{MO : @MeasureOmegaInterface M MI} := {
  meas_lub_unique : forall {A} (chain : nat -> M A) mu nu,
      meas_lub chain mu -> meas_lub chain nu -> meas_eq mu nu;
  meas_lub_proper : forall {A} (c1 c2 : nat -> M A) mu,
      (forall n, meas_eq (c1 n) (c2 n)) ->
      meas_lub c1 mu -> meas_lub c2 mu
}.

Section Iteration.
Context {M : Type -> Type} `{MI : MeasureInterface M}
  `{MO : @MeasureOmegaInterface M MI}.

(** The [n]-step submeasure of an absorbing probabilistic loop.  A left
    result continues with one less unit of fuel; a right result is absorbed.
    Runs which have not terminated within the fuel budget contribute zero
    mass. *)
Fixpoint meas_iter_approx {I A}
    (n : nat) (step : I -> M (I + A)) (i : I) : M A :=
  match n with
  | O => meas_zero
  | S n' =>
      meas_bind (step i) (fun next =>
        match next with
        | inl i' => meas_iter_approx n' step i'
        | inr a => meas_ret a
        end)
  end.

(** An unbounded iteration denotes precisely a limit of all its finite
    absorbing approximations.  This is a relation because a representation
    such as finite rational [Enum] is not closed under every omega-limit. *)
Definition meas_iter {I A} (step : I -> M (I + A))
    (i : I) (out : M A) : Prop :=
  meas_lub (fun n => meas_iter_approx n step i) out.

Lemma meas_iter_unique `{OL : @MeasureOmegaLaws M MI MO}
    {I A} (step : I -> M (I + A)) i out1 out2 :
  meas_iter step i out1 -> meas_iter step i out2 -> meas_eq out1 out2.
Proof.
  unfold meas_iter. eapply meas_lub_unique.
Qed.

End Iteration.
