(** Actual rewrite clients, heterogeneous probabilistic bind, and eventful
    naturality/codiagonal. Ordinary algebra laws are tested at their generic
    owner; handler clients live with the handler regressions. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.EnumQ.Representation.
From PTree.Prob.Interface Require Import FrontierLift.
Require Import PTree.Prob.Backend.EnumQ.FrontierLift.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.EnumQ.Iteration.
From PTree.Eq Require Import PTreeKernel ProbabilisticTrace.
From PTree.Eq.FreeOmega Require Import Base Hitting Relation Bind Algebra Iter.
From PTree.Eq Require Import PEutt PStruct PStrong.
From PTree.Regression.Backend Require Import EnumQMeasureRegression.
Require Import PTree.Interp.FreeOmega.Translate.
From PTree.Interp.FreeOmega Require Import Base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.

Variant algebraE : Type -> Type := .
Local Notation MF := (FreeOmega EnumQ).
Local Notation peutt :=
  (@PEutt.peutt algebraE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega).

(** Pin this regression's observable profile before setoid search. These are
    local specializations of the single generic proofs, not backend laws. *)
#[local] Instance regression_bind_Proper {A B} :
  Proper (peutt eq ==> pointwise_relation A (peutt eq) ==> peutt eq)
    (@PTree.bind algebraE EnumQ A B).
Proof. apply peutt_bind_Proper. Qed.

#[local] Instance regression_fmap_Proper {A B} (f : A -> B) :
  Proper (peutt eq ==> peutt eq) (@PTree.fmap algebraE EnumQ A B f).
Proof. apply peutt_fmap_Proper. Qed.

(** Regression: the bind [Proper] instance supports rewriting a canonical
    equivalence underneath a continuation. *)
Lemma canonical_bind_setoid_rewrite {A B}
    (t1 t2 : ptree algebraE EnumQ A)
    (k : A -> ptree algebraE EnumQ B) :
  peutt eq t1 t2 ->
  peutt eq (PTree.bind t1 k) (PTree.bind t2 k).
Proof.
  intro Ht. setoid_rewrite Ht. reflexivity.
Qed.

Variant bindE : Type -> Type := BindAsk : bindE bool.
Local Notation bindW := (@PEutt.peutt bindE EnumQ MF
  (FreeOmegaObservableSemanticMeasure
    (NI := EnumQ_SemanticMeasure) (NO := EnumQ_SemanticOmega))
  FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
  FreeOmegaObservableSemanticOmega).

Definition bind_source_rel (b : bool) (n : nat) :=
  n = if b then 1 else 0.
Definition bind_result_rel (n : nat) (b : bool) :=
  n = if b then 2 else 3.

(** A real probabilistic/eventful client: bool/nat at the source and
    nat/bool at the result, with different non-equality relations. *)
Example eventful_heterogeneous_bind :
  bindW bind_result_rel
    (PTree.bind
      (Vis BindAsk (fun _ => Prob reg_fair (fun b => Ret b)))
      (fun b => Tau (Ret (if b then 2 else 3))))
    (PTree.bind
      (Vis BindAsk (fun _ => Prob reg_fair
        (fun b => Ret (if b then 1 else 0))))
      (fun n => Ret (Nat.eqb n 1))).
Proof.
  eapply Bind.peutt_bind with (RR := bind_source_rel).
  - apply peutt_of_pstruct.
    apply pstruct_fold. constructor. intro response.
    apply pstruct_fold. constructor. intro b.
    apply pstruct_fold. constructor. reflexivity.
  - intros b n Hn. unfold bind_source_rel in Hn. subst n.
    eapply peutt_of_hitting_lift.
    + apply (proj2 (stable_hitting_tau_iff _ _)).
      apply stable_hitting_ret.
    + apply stable_hitting_ret.
    + apply sem_lift_ret. constructor. destruct b; reflexivity.
Qed.

(** Regression: the Functor [Proper] instance is registered with the setoid
    machinery, not merely available as a manually applied theorem. *)
Lemma canonical_fmap_setoid_rewrite {A B}
    (f : A -> B) (t1 t2 : ptree algebraE EnumQ A) :
  peutt eq t1 t2 -> peutt eq (PTree.fmap f t1) (PTree.fmap f t2).
Proof.
  intro Ht. setoid_rewrite Ht. reflexivity.
Qed.

(** Measure rewriting uses coupling equality, so a split representation of
    the fair distribution rewrites under [Prob] without list equality. *)
Lemma canonical_prob_measure_setoid_rewrite {R}
    (k : bool -> ptree algebraE EnumQ R) :
  peutt eq (Prob reg_fair k) (Prob reg_fair_split k).
Proof.
  set (sample := fun mu : EnumQ bool =>
    (Prob mu k : ptree algebraE EnumQ R)).
  change (peutt eq (sample reg_fair) (sample reg_fair_split)).
  assert (Hsample : Proper
      (@sem_lift EnumQ EnumQ_SemanticMeasure bool bool eq ==>
       peutt eq) sample).
  { intros mu1 mu2 Hmu. unfold sample.
    apply peutt_prob_measure. exact Hmu. }
  setoid_rewrite reg_split_mass_lift_eq. reflexivity.
Qed.

Variant naturalityE : Type -> Type :=
  | ReadFlag : naturalityE bool.

Local Notation naturality_peutt :=
  (@PEutt.peutt naturalityE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega).

Definition naturality_step (_ : unit) :
    ptree naturalityE EnumQ (unit + bool) :=
  Vis ReadFlag (fun observed =>
    Prob reg_fair (fun retry =>
      Ret (if retry then inl tt else inr observed))).

Definition naturality_post (b : bool) : ptree naturalityE EnumQ nat :=
  Tau (Ret (if b then 1 else 0)).

(** Naturality is exercised by an eventful, probabilistic, potentially
    unbounded retry loop; it is not merely a finite countdown equation. *)
Lemma canonical_iter_natural_regression :
  naturality_peutt eq
    (PTree.bind (PTree.iter naturality_step tt) naturality_post)
    (PTree.iter
      (pstruct_iter_natural_step (E := naturalityE) (M := EnumQ)
        naturality_step naturality_post) tt).
Proof. apply peutt_iter_natural. Qed.

Definition codiagonal_step (_ : unit) :
    ptree naturalityE EnumQ (unit + (unit + bool)) :=
  Vis ReadFlag (fun observed : bool =>
    Prob reg_fair (fun choose_inner : bool =>
      Ret ((if observed then
        if choose_inner then inl tt else inr (inl tt)
      else inr (inr false)) : unit + (unit + bool)))).

(** Both retry layers are live: the visible answer selects termination versus
    retry, while the fair sample selects an inner versus outer retry. *)
Lemma canonical_iter_codiagonal_regression :
  naturality_peutt eq
    (PTree.iter (fun j => PTree.iter codiagonal_step j) tt)
    (PTree.iter
      (pstruct_iter_codiagonal_flat_step codiagonal_step) tt).
Proof. apply peutt_iter_codiagonal. Qed.

Variant sourceE : Type -> Type :=
  | AskBit : sourceE bool.

Variant renamedE : Type -> Type :=
  | GetBit : renamedE bool.

Definition rename_bit (X : Type) (e : sourceE X) : renamedE X :=
  match e with
  | AskBit => GetBit
  end.

Lemma canonical_translate_setoid_rewrite {A}
    (t1 t2 : ptree sourceE EnumQ A) :
  @PEutt.peutt sourceE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A A eq t1 t2 ->
  @PEutt.peutt renamedE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A A eq
    (PTree.translate rename_bit t1) (PTree.translate rename_bit t2).
Proof.
  intro Ht. setoid_rewrite Ht. reflexivity.
Qed.
