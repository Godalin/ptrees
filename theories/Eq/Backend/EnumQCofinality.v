(** Role: Canonical equational/hitting theory. Depends on Core and Prob; does not provide comparison or interpreter semantics. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import List.
From Coq.Arith Require Import PeanoNat.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.EnumQ.Representation.
Require Import PTree.Prob.Backend.EnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import PTreeKernel.
From PTree.Eq.FreeOmega Require Import Base Relation Bind.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Backend-specific finite-support facts.  They are kept outside the generic
    FreeOmega development because the uniform bound below is a property of
    EnumQ's finite representation, not of the semantic measure interface. *)
Section EnumQCofinality.
Import EnumQ.
Context {E : Type -> Type}.

Lemma enumQ_uniform_nat_bound {X} (mu : EnumQ X) (P : X -> nat -> Prop) :
  (forall x, exists n, P x n) ->
  (forall x n m, Peano.le n m -> P x n -> P x m) ->
  exists n, forall p x, List.In (p, x) mu -> P x n.
Proof.
  intros Hex Hmono. induction mu as [|[p x] mu IH].
  - exists 0. intros q y Hin. inversion Hin.
  - destruct (Hex x) as [nx Hx].
    destruct IH as [nt Htail].
    exists (Nat.max nx nt). intros q y [Hhead|Hin].
    + inversion Hhead; subst. eapply Hmono; [apply Nat.le_max_l|exact Hx].
    + eapply Hmono; [apply Nat.le_max_r|exact (Htail _ _ Hin)].
Qed.

Theorem enumQ_bind_prob_uniform {A R X}
    (mu : EnumQ X) (c : X -> ptree E EnumQ A)
    (k : A -> ptree E EnumQ R) :
  (forall x, ptree_bind_approx_cofinal (c x) k) ->
  ptree_bind_prob_uniform mu c k.
Proof.
  intro Hbranches. split.
  - intro fuel.
    destruct (enumQ_uniform_nat_bound mu
      (P := fun x bound => free_omega_approx eq
        (ptree_hitting_approx (MF := FreeOmega EnumQ) fuel
          (observe (PTree.bind (c x) k)))
        (ptree_bind_diagonal_approx (MF := FreeOmega EnumQ)
          bound (c x) k))) as [bound Hbound].
    + intro x. exact (proj1 (Hbranches x) fuel).
    + intros x n m Hnm Happrox.
      eapply free_omega_approx_trans; [exact Happrox|].
      apply ptree_bind_diagonal_mono. exact Hnm.
    + exists bound,
        (fun x => free_omega_approx eq
          (ptree_hitting_approx (MF := FreeOmega EnumQ) fuel
            (observe (PTree.bind (c x) k)))
          (ptree_bind_diagonal_approx (MF := FreeOmega EnumQ)
            bound (c x) k)).
      split.
      * intros p x Hin _. exact (Hbound p x Hin).
      * intros x Hx. exact Hx.
  - intro fuel.
    destruct (enumQ_uniform_nat_bound mu
      (P := fun x bound => free_omega_approx eq
        (ptree_bind_diagonal_approx (MF := FreeOmega EnumQ)
          fuel (c x) k)
        (ptree_hitting_approx (MF := FreeOmega EnumQ) bound
          (observe (PTree.bind (c x) k))))) as [bound Hbound].
    + intro x. destruct (proj2 (Hbranches x) fuel) as [n Hn].
      exists n. eapply free_omega_approx_mono; [|exact Hn].
      intros a b Hba. symmetry. exact Hba.
    + intros x n m Hnm Happrox.
      eapply free_omega_approx_trans; [exact Happrox|].
      apply ptree_hitting_mono. exact Hnm.
    + exists bound,
        (fun x => free_omega_approx eq
          (ptree_bind_diagonal_approx (MF := FreeOmega EnumQ)
            fuel (c x) k)
          (ptree_hitting_approx (MF := FreeOmega EnumQ) bound
            (observe (PTree.bind (c x) k)))).
      split.
      * intros p x Hin _. exact (Hbound p x Hin).
      * intros x Hx. exact Hx.
Qed.

Corollary enumQ_bind_prob_approx_cofinal {A R X}
    (mu : EnumQ X) (c : X -> ptree E EnumQ A)
    (k : A -> ptree E EnumQ R) :
  (forall x, ptree_bind_approx_cofinal (c x) k) ->
  ptree_bind_approx_cofinal (Prob mu c) k.
Proof.
  intro Hbranches. apply ptree_bind_prob_approx_cofinal.
  exact (enumQ_bind_prob_uniform
    mu (c := c) (k := k) Hbranches).
Qed.

End EnumQCofinality.
