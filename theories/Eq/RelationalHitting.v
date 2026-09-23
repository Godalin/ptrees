(** Relational simulation of finite kernel execution and its increasing
    limit. No tree syntax or concrete frontier representation is used. *)
Set Universe Polymorphism.
From PTree.Prob.Interface Require Import Measure Omega RelationalClosure.
From PTree.Eq Require Import PrimitiveStableHitting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition stable_target_rel {S1 S2 A B}
    (SR : S1 -> S2 -> Prop) (AR : A -> B -> Prop)
    (x : stable_target S1 A) (y : stable_target S2 B) : Prop :=
  match x, y with
  | SHStable a, SHStable b => AR a b
  | SHInternal s, SHInternal t => SR s t
  | _, _ => False
  end.

Section RelationalHitting.
Context {MF : Type -> Type} `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FO : @SemanticOmega MF FI}.
Variable Hbind : relational_bind FI.
Variable Hzero : relational_zero FO.
Context {S1 S2 A B : Type}.
Variable kernel1 : S1 -> MF (stable_target S1 A).
Variable kernel2 : S2 -> MF (stable_target S2 B).
Variable SR : S1 -> S2 -> Prop.
Variable AR : A -> B -> Prop.
Hypothesis Hkernel : forall s t, SR s t ->
  sem_lift (stable_target_rel SR AR) (kernel1 s) (kernel2 t).

Lemma stable_target_approx_rel fuel x y :
  stable_target_rel SR AR x y ->
  sem_lift AR (stable_target_approx kernel1 fuel x)
    (stable_target_approx kernel2 fuel y).
Proof.
  revert x y. induction fuel as [|fuel IH];
    intros [a|s] [b|t] H; simpl in *; try contradiction.
  - apply sem_lift_ret. exact H.
  - apply Hzero.
  - apply sem_lift_ret. exact H.
  - eapply Hbind; [apply Hkernel; exact H|exact IH].
Qed.

Theorem stable_hitting_approx_rel fuel s t : SR s t ->
  sem_lift AR (stable_hitting_approx kernel1 fuel s)
    (stable_hitting_approx kernel2 fuel t).
Proof.
  intro H. unfold stable_hitting_approx.
  eapply Hbind; [apply Hkernel; exact H|apply stable_target_approx_rel].
Qed.

Context `{FOrd : @SemanticMeasureOrderLaws MF FI FO}.
Variable Hlimit : relational_lub FO.

Theorem stable_hitting_rel s t mu nu :
  SR s t -> stable_hitting kernel1 s mu -> stable_hitting kernel2 t nu ->
  sem_lift AR mu nu.
Proof.
  intros H Hmu Hnu. eapply Hlimit.
  - exact (stable_hitting_increasing kernel1 s).
  - exact (stable_hitting_increasing kernel2 t).
  - exact Hmu.
  - exact Hnu.
  - intro n. apply stable_hitting_approx_rel. exact H.
Qed.
End RelationalHitting.
