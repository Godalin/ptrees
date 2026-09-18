Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Well-founded internal execution to a distribution of residual trees.
    Stop need not be stable.  Each branch has a well-founded derivation;
    an infinitely branching sampling node need not have a uniform finite
    depth bound.  This judgment contains neither fuel nor stable hitting. *)
Section FiniteInternal.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}.
Context {R : Type}.

Inductive finite_internal : ptree E MN R -> MF (ptree E MN R) -> Prop :=
  | FIStop t : finite_internal t (sem_ret t)
  | FITau t out : finite_internal t out -> finite_internal (Tau t) out
  | FIProb {X} (mu : MN X) (k : X -> ptree E MN R)
      (out : X -> MF (ptree E MN R)) :
      (forall x, finite_internal (k x) (out x)) ->
      finite_internal (Prob mu k) (mixed_bind mu out).

Fixpoint tau_prefix (n : nat) (t : ptree E MN R) : ptree E MN R :=
  match n with O => t | S m => Tau (tau_prefix m t) end.

Lemma finite_internal_tau_prefix n t :
  finite_internal (tau_prefix n t) (sem_ret t).
Proof. induction n; [apply FIStop|apply FITau; exact IHn]. Qed.

Lemma finite_internal_prob_tau_prefix {X} (mu : MN X)
    (depth : X -> nat) (k : X -> ptree E MN R) :
  finite_internal (Prob mu (fun x => tau_prefix (depth x) (k x)))
    (mixed_bind mu (fun x => sem_ret (k x))).
Proof. apply FIProb. intro x. apply finite_internal_tau_prefix. Qed.

Lemma finite_internal_ret_inv r out :
  finite_internal (Ret r) out -> out = sem_ret (Ret r).
Proof. intro H. inversion H; reflexivity. Qed.

(** A deterministic silent self-loop cannot be compressed away: every
    well-founded derivation leaves precisely that loop as its residual. *)
Lemma finite_internal_self_loop_inv t out :
  finite_internal t out -> observe t = TauF t -> out = sem_ret t.
Proof.
  intro H. induction H; intro Hloop.
  - reflexivity.
  - cbn in Hloop. injection Hloop as Heq.
    assert (Hself : observe t = TauF t).
    { rewrite Heq at 1. reflexivity. }
    rewrite (IHfinite_internal Hself). now rewrite Heq at 1.
  - discriminate Hloop.
Qed.

End FiniteInternal.
