(** Role: Public-only client contract. No implementation imports or local
    capability registrations: both return carriers and relations are free. *)
Set Universe Polymorphism.
From PTree Require Import PTree PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ.
From Coq Require Import Morphisms.

Local Notation MN := SubEnumQ.

Section PublicBind.
Context {E : Type -> Type} {A B R1 R2 : Type}.
Context (RR : R1 -> R2 -> Prop) (RS : A -> B -> Prop).
Context (t1 : ptree E MN R1) (t2 : ptree E MN R2).
Context (k1 : R1 -> ptree E MN A) (k2 : R2 -> ptree E MN B).

Example public_heterogeneous_bind
    (Ht : t1 ≈ₚ[RR] t2)
    (Hk : forall x y, RR x y -> k1 x ≈ₚ[RS] k2 y) :
  bind t1 k1 ≈ₚ[RS] bind t2 k2.
Proof.
  (** RR occurs only in the premises: ordinary apply cannot infer it from
      the conclusion. Keep this boundary visible instead of guessing a
      return relation through typeclass search. *)
  Fail apply peutt_bind.
  eapply peutt_bind; eassumption.
Qed.

Example public_heterogeneous_bind_explicit
    (Ht : t1 ≈ₚ[RR] t2)
    (Hk : forall x y, RR x y -> k1 x ≈ₚ[RS] k2 y) :
  bind t1 k1 ≈ₚ[RS] bind t2 k2.
Proof. apply (peutt_bind (RR := RR)); assumption. Qed.
End PublicBind.

Example public_reflexivity {E A} (t : ptree E MN A) : t ≈ₚ t.
Proof. apply peutt_refl. Qed.

Example public_tau {E A} (t : ptree E MN A) : Tau t ≈ₚ t.
Proof. apply peutt_tau_l. Qed.

Example public_related_returns {E A B} (RR : A -> B -> Prop)
    (a : A) (b : B) (H : RR a b) :
  (Ret a : ptree E MN A) ≈ₚ[RR] (Ret b : ptree E MN B).
Proof. apply peutt_ret; assumption. Qed.

Fail Check free_omega_qlift.
(** Direct theorem exports intentionally expose their owning module's
    helpers. The old alias facade's short-name hiding is no longer policy. *)
Check ptree_bind_cofinal_all.
Fail Check PTree.Eq.Backend.MathComp.Direct.MathComp_CanonicalBehavior.

(** Importing the raw owner last must not shadow the unconditional theorem. *)
From PTree.Eq Require Import PEutt.
Definition public_bind_owner := @peutt_bind.
Definition generic_bind_owner := @peutt_bind_cofinal.

Example public_structural_return {E A B} (RR : A -> B -> Prop)
    (a : A) (b : B) (H : RR a b) :
  (Ret a : ptree E MN A) ≡ₚ[RR] (Ret b : ptree E MN B).
Proof. apply pstruct_fold. constructor. assumption. Qed.

Example public_strong_return {E A B} (RR : A -> B -> Prop)
    (a : A) (b : B) (H : RR a b) :
  (Ret a : ptree E MN A) ≃ₚ[RR] (Ret b : ptree E MN B).
Proof. apply pstrong_ret_intro; assumption. Qed.

Example public_bind_after_raw_import {E A B X Y}
    (RR : X -> Y -> Prop) (RS : A -> B -> Prop)
    (t : ptree E MN X) (u : ptree E MN Y)
    (k : X -> ptree E MN A) (l : Y -> ptree E MN B)
    (Ht : t ≈ₚ[RR] u) (Hk : forall x y, RR x y -> k x ≈ₚ[RS] l y) :
  bind t k ≈ₚ[RS] bind u l.
Proof. eapply peutt_bind; eassumption. Qed.

(** Fix the intended relation locally before setoid search; the actual Proper
    proof is generic. No concrete completion or new global hint is needed. *)
Example public_bind_setoid {E A B} (t u : ptree E MN A)
    (k : A -> ptree E MN B) (H : t ≈ₚ u) :
  bind t k ≈ₚ bind u k.
Proof.
  assert (Hp : Proper ((fun a b => a ≈ₚ b) ==>
    pointwise_relation A (fun a b => a ≈ₚ b) ==> (fun a b => a ≈ₚ b))
    (@PTree.bind E MN A B)) by apply peutt_bind_Proper.
  Timeout 10 setoid_rewrite H. apply peutt_refl.
Qed.

Example public_continuation_setoid {E A B} (t : ptree E MN A)
    (k h : A -> ptree E MN B) (H : forall x, k x ≈ₚ h x) :
  bind t k ≈ₚ bind t h.
Proof.
  assert (Hp : Proper ((fun a b => a ≈ₚ b) ==>
    pointwise_relation A (fun a b => a ≈ₚ b) ==> (fun a b => a ≈ₚ b))
    (@PTree.bind E MN A B)) by apply peutt_bind_Proper.
  assert (Hpoint : pointwise_relation A (fun a b => a ≈ₚ b) k h) by exact H.
  Timeout 10 setoid_rewrite Hpoint. apply peutt_refl.
Qed.

Example public_fmap_setoid {E A B} (f : A -> B)
    (t u : ptree E MN A) (H : t ≈ₚ u) :
  PTree.fmap f t ≈ₚ PTree.fmap f u.
Proof.
  assert (Hp : Proper ((fun a b => a ≈ₚ b) ==> (fun a b => a ≈ₚ b))
    (@PTree.fmap E MN A B f)) by apply peutt_fmap_Proper.
  Timeout 10 setoid_rewrite H. apply peutt_refl.
Qed.
