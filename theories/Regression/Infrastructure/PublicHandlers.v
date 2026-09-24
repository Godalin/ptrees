(** Public-only handler clients: no implementation imports or route hints. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree Require Import PTree PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ.
From Coq Require Import Morphisms.
From ITree.Indexed Require Import Sum.
Set Implicit Arguments.

Variant requestE : Type -> Type := Request : requestE bool.
Variant answerE : Type -> Type := Answer : bool -> answerE unit.

Definition immediate X (e : requestE X) : ptree answerE SubEnumQ X :=
  match e with Request => Ret true end.
Definition delayed X (e : requestE X) : ptree answerE SubEnumQ X :=
  Tau (immediate e).

Lemma immediate_delayed X (e : requestE X) : immediate e ≈ₚ delayed e.
Proof. apply peutt_tau_r. Qed.

(** The new premise is genuinely weaker than structural replacement. *)
Example replacement_not_structural : ~ pstruct eq (immediate Request) (delayed Request).
Proof. intro H. pose proof (pstruct_unfold H) as Hstep. inversion Hstep. Qed.

Example public_handler_replacement {A B} (RR : A -> B -> Prop)
    (t : ptree requestE SubEnumQ A) (u : ptree requestE SubEnumQ B) :
  t ≈ₚ[RR] u -> interp immediate t ≈ₚ[RR] interp delayed u.
Proof.
  intro H. eapply free_omega_peutt_interp_handler_rel; [|exact H].
  intros X e. apply immediate_delayed.
Qed.

CoFixpoint infinite_service : ptree requestE SubEnumQ unit :=
  Vis Request (fun _ => infinite_service).

Example returning_handlers_on_infinite_source :
  interp immediate infinite_service ≈ₚ interp delayed infinite_service.
Proof. apply public_handler_replacement. apply peutt_refl. Qed.

Example different_return_carriers :
  interp immediate (Vis Request (fun b => Ret b)) ≈ₚ[fun (b : bool) (n : nat) => n = if b then 1 else 0]
  interp delayed (Vis Request (fun b : bool => Ret (if b then 1 else 0))).
Proof.
  apply public_handler_replacement. apply peutt_vis. intro b. apply peutt_ret. reflexivity.
Qed.

(** A real setoid rewrite of the handler argument, with an explicit local
    Proper witness. No global search for handler equality is installed. *)
Definition public_handler_rel (h g : Handler SubEnumQ requestE answerE) :=
  forall X (e : requestE X), h X e ≈ₚ g X e.

#[local] Instance public_interp_Proper :
  Proper (public_handler_rel ==> forall_relation (fun A : Type =>
    (fun t u : ptree requestE SubEnumQ A => t ≈ₚ u) ==>
    (fun t u : ptree answerE SubEnumQ A => t ≈ₚ u)))
    (@PTree.interp requestE answerE SubEnumQ).
Proof. apply free_omega_peutt_interp_handler_polymorphic_Proper. Qed.

Example rewriting_handler {A} (t : ptree requestE SubEnumQ A) :
  interp immediate t ≈ₚ interp delayed t.
Proof.
  assert (H : public_handler_rel immediate delayed) by exact immediate_delayed.
  setoid_rewrite H. apply peutt_refl.
Qed.

Example public_left_unit {E F} (h : Handler SubEnumQ E F) X (e : E X) :
  Handler.cat Handler.id_ h e ≈ₚ h X e.
Proof. apply free_omega_handler_cat_id_l. Qed.

Example public_right_unit {E F} (h : Handler SubEnumQ E F) X (e : E X) :
  Handler.cat h Handler.id_ e ≈ₚ h X e.
Proof. apply free_omega_handler_cat_id_r. Qed.

Example public_associativity {E F G H} (h : Handler SubEnumQ E F)
    (g : Handler SubEnumQ F G) (k : Handler SubEnumQ G H) X (e : E X) :
  Handler.cat (Handler.cat h g) k e ≈ₚ Handler.cat h (Handler.cat g k) e.
Proof. apply free_omega_handler_cat_assoc. Qed.

Example public_case_beta :
  Handler.cat Handler.inl_ (Handler.case_ immediate immediate) Request ≈ₚ immediate Request.
Proof. apply free_omega_handler_case_inl. Qed.

Example public_bimap_replacement X (e : (requestE +' requestE) X) :
  Handler.bimap immediate immediate e ≈ₚ Handler.bimap delayed delayed e.
Proof.
  apply free_omega_handler_bimap_congr; intros Y a; apply immediate_delayed.
Qed.

(** All pure combinators remain usable above Set. *)
Section HighUniverse.
Universe hi.
Constraint Set < hi.
Definition high_handler : Handler SubEnumQ (fun X => Type@{hi}) (fun X => Type@{hi}) :=
  Handler.id_.
Check (Handler.bimap high_handler high_handler).
End HighUniverse.

Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Eq.Backend.MathComp.Direct.MathComp_CanonicalBehavior.
