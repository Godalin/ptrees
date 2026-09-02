Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import List Arith.PeanoNat.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import DiscreteMC FreeOmegaMeasure.
From PTree.Eq Require Import
  OperationalProbabilisticPTS OperationalProbabilisticPTSFreeOmegaBase.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Backend-specific finite-support facts.  They are kept outside the generic
    FreeOmega development because the uniform bound below is a property of
    Enum's finite representation, not of the semantic measure interface. *)
Section EnumOperationalCofinality.
Import Enum.
Context {E : Type -> Type}.

Lemma enum_uniform_nat_bound {X} (mu : Enum X) (P : X -> nat -> Prop) :
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

Theorem enum_free_operational_bind_prob_uniform {A R X}
    (mu : Enum X) (c : X -> ptree E Enum A)
    (k : A -> ptree E Enum R) :
  (forall x, free_operational_bind_approx_cofinal (c x) k) ->
  free_operational_bind_prob_uniform mu c k.
Proof.
  intro Hbranches. split.
  - intro fuel.
    destruct (enum_uniform_nat_bound mu
      (P := fun x bound => free_omega_approx eq
        (operational_hitting_approx (MF := FreeOmega Enum) fuel
          (observe (PTree.bind (c x) k)))
        (operational_bind_diagonal_approx (MF := FreeOmega Enum)
          bound (c x) k))) as [bound Hbound].
    + intro x. exact (proj1 (Hbranches x) fuel).
    + intros x n m Hnm Happrox.
      eapply free_omega_approx_trans; [exact Happrox|].
      apply free_operational_bind_diagonal_mono. exact Hnm.
    + exists bound,
        (fun x => free_omega_approx eq
          (operational_hitting_approx (MF := FreeOmega Enum) fuel
            (observe (PTree.bind (c x) k)))
          (operational_bind_diagonal_approx (MF := FreeOmega Enum)
            bound (c x) k)).
      split.
      * intros p x Hin _. exact (Hbound p x Hin).
      * intros x Hx. exact Hx.
  - intro fuel.
    destruct (enum_uniform_nat_bound mu
      (P := fun x bound => free_omega_approx eq
        (operational_bind_diagonal_approx (MF := FreeOmega Enum)
          fuel (c x) k)
        (operational_hitting_approx (MF := FreeOmega Enum) bound
          (observe (PTree.bind (c x) k))))) as [bound Hbound].
    + intro x. destruct (proj2 (Hbranches x) fuel) as [n Hn].
      exists n. eapply free_omega_approx_mono; [|exact Hn].
      intros a b Hba. symmetry. exact Hba.
    + intros x n m Hnm Happrox.
      eapply free_omega_approx_trans; [exact Happrox|].
      apply free_operational_hitting_mono. exact Hnm.
    + exists bound,
        (fun x => free_omega_approx eq
          (operational_bind_diagonal_approx (MF := FreeOmega Enum)
            fuel (c x) k)
          (operational_hitting_approx (MF := FreeOmega Enum) bound
            (observe (PTree.bind (c x) k)))).
      split.
      * intros p x Hin _. exact (Hbound p x Hin).
      * intros x Hx. exact Hx.
Qed.

Corollary enum_free_operational_bind_prob_approx_cofinal {A R X}
    (mu : Enum X) (c : X -> ptree E Enum A)
    (k : A -> ptree E Enum R) :
  (forall x, free_operational_bind_approx_cofinal (c x) k) ->
  free_operational_bind_approx_cofinal (Prob mu c) k.
Proof.
  intro Hbranches. apply free_operational_bind_prob_approx_cofinal.
  exact (enum_free_operational_bind_prob_uniform
    mu (c := c) (k := k) Hbranches).
Qed.

End EnumOperationalCofinality.
