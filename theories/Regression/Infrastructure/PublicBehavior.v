(** Role: Public-only client contract. No implementation imports or local
    capability registrations: both return carriers and relations are free. *)
Set Universe Polymorphism.
From PTree Require Import PTree.
From PTree.API Require Import SubEnumQ.

Local Notation MN := PTree.Prob.Backend.SubEnumQ.Representation.SubEnumQ.

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
Fail Check ptree_bind_cofinal_all.
Fail Check PTree.Eq.Backend.MathComp.Direct.MathComp_CanonicalBehavior.
