(** Interpreted effect equations, noncommutative logs, and missing mass. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From ExtLib.Structures Require Import Monoid BinOps.
From ITree.Basics Require Import Basics.
From ITree.Events Require Import Reader State Writer Exception.
From ITree.Indexed Require Import Sum.
From PTree Require Import PTree PTreeFacts.
From PTree.Interp.Algebra Require Import Computation Reader State Writer Exception.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Eq.Backend.MathComp.Direct.MathComp_CanonicalBehavior.
From PTree.Eq.Backend Require Import SubEnumQ.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

Example reader_repeated {E A} (k : nat -> nat -> ptree (readerE nat +' E) SubEnumQ A) env :
  run_reader (Vis (inl1 Ask) (fun x => Vis (inl1 Ask) (k x))) env ≈ₚ
  run_reader (Vis (inl1 Ask) (fun x => k x x)) env.
Proof. apply run_reader_ask_ask. Qed.

Example state_restore {E A} (k : ptree (stateE nat +' E) SubEnumQ A) s :
  run_state (Vis (inl1 (Get nat)) (fun x => Vis (inl1 (Put nat x)) (fun _ => k))) s ≈ₚ
  run_state k s.
Proof. apply run_state_get_put. Qed.

Example state_overwrite {E A} (k : ptree (stateE nat +' E) SubEnumQ A) s a b :
  run_state (Vis (inl1 (Put nat a)) (fun _ => Vis (inl1 (Put nat b)) (fun _ => k))) s ≈ₚ
  run_state (Vis (inl1 (Put nat b)) (fun _ => k)) s.
Proof. apply run_state_put_put. Qed.

Example state_draw_swap {E A X} (mu : SubEnumQ X)
    (k : nat -> X -> ptree (stateE nat +' E) SubEnumQ A) s :
  run_state (Vis (inl1 (Get nat)) (fun v => Prob mu (k v))) s ≈ₚ
  run_state (Prob mu (fun x => Vis (inl1 (Get nat)) (fun v => k v x))) s.
Proof. apply run_state_get_prob. Qed.

Definition log_op : Monoid (list nat) := {| monoid_plus := @app nat; monoid_unit := [] |}.
#[local] Instance log_laws : MonoidLaws log_op.
Proof.
  constructor; unfold Associative, LeftUnit, RightUnit; cbn.
  - intros. symmetry. apply app_assoc.
  - intros. reflexivity.
  - apply app_nil_r.
Qed.

Example writer_fusion {E A} a b (k : ptree (writerE (list nat) +' E) SubEnumQ A) :
  run_writer log_op (Vis (inl1 (Tell a)) (fun _ => Vis (inl1 (Tell b)) (fun _ => k))) ≈ₚ
  run_writer log_op (Vis (inl1 (Tell (a ++ b))) (fun _ => k)).
Proof. apply run_writer_tell_append. exact log_laws. Qed.

Example writer_unit {E A} (k : ptree (writerE (list nat) +' E) SubEnumQ A) :
  run_writer log_op (Vis (inl1 (Tell [])) (fun _ => k)) ≈ₚ run_writer log_op k.
Proof. apply run_writer_tell_unit. exact log_laws. Qed.

Example log_monoid_not_commutative : monoid_plus log_op [1] [2] <> monoid_plus log_op [2] [1].
Proof. discriminate. Qed.

Example writer_log_order :
  run_writer log_op
    (Vis (inl1 (Tell [1])) (fun _ => Vis (inl1 (Tell [2])) (fun _ =>
      (Ret tt : ptree (writerE (list nat) +' void1) SubEnumQ unit)))) ≈ₚ Ret ([1;2],tt).
Proof.
  change (run_writer_from log_op
    (Vis (inl1 (Tell [1])) (fun _ => Vis (inl1 (Tell [2])) (fun _ => Ret tt))) [] ≈ₚ
      (Ret ([1;2],tt) : ptree void1 SubEnumQ (list nat * unit))).
  eapply peutt_trans; [apply run_writer_from_tell|].
  eapply peutt_trans; [apply run_writer_from_tell|].
  apply peutt_observe_eq. reflexivity.
Qed.

Example writer_draw_swap {E A X} (mu : SubEnumQ X) w
    (k : X -> ptree (writerE (list nat) +' E) SubEnumQ A) :
  run_writer log_op (Vis (inl1 (Tell w)) (fun _ => Prob mu k)) ≈ₚ
  run_writer log_op (Prob mu (fun x => Vis (inl1 (Tell w)) (fun _ => k x))).
Proof. apply run_writer_tell_prob; typeclasses eauto. Qed.

Example exception_left_zero {E A B} err (k : A -> ptree (exceptE nat +' E) SubEnumQ B) :
  run_exception (PTree.bind (Vis (inl1 (Throw err)) (fun v : void => match v with end)) k) ≈ₚ
  Ret (inl err).
Proof. apply run_exception_throw_bind. Qed.

(** Stronger than an execution-only counterexample: unequal complete mass
    rules out peutt even though both successful outcomes throw the same error. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Backend.SubEnumQ Require Import Expectation Measure.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import UpperExpectation UpperQuotient.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Prob.FreeOmega Require Import StructuralMeasure.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel PEutt.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Definition half_entries : list (rat * unit) := [(2^-1,tt)].
Lemma half_nonnegative : finite_nonnegative half_entries.
Proof. intros p x [H|[]]; inversion H; subst; native_compute; reflexivity. Qed.
Lemma half_bounded : finite_expect (fun _ => 1) half_entries <= 1.
Proof. native_compute; reflexivity. Qed.
Definition half_sample := subenumQ_of_list half_nonnegative half_bounded.
Definition raises : ptree (exceptE nat +' void1) SubEnumQ unit :=
  Vis (inl1 (Throw 7%nat)) (fun v : void => match v with end).
Definition sample_then_raise := Prob half_sample (fun _ => raises).

Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Definition error_head : stable_head void1 SubEnumQ (nat+unit) := FHRet (inl 7%nat).
Definition partial_error_front : MF (stable_head void1 SubEnumQ (nat+unit)) :=
  FOSample half_sample (fun _ => FORet error_head).

Lemma partial_error_hitting :
  ptree_stable_hitting (FI := FI) (FO := FO)
    (observe (run_exception sample_then_raise)) partial_error_front.
Proof.
  change (ptree_stable_hitting (FI := FI) (FO := FO)
    (observe (Prob half_sample (fun _ => run_exception raises))) partial_error_front).
  apply (stable_hitting_prob (FI := FI) (MX := FreeOmegaMixedMeasure)
    (front := fun _ : unit => FORet error_head) (Good := fun _ => True)).
  - apply sem_ae_true.
  - intros [] _. change (ptree_stable_hitting (FI := FI) (FO := FO)
      (observe (Ret (inl 7%nat))) (FORet error_head)).
    apply (ptree_stable_hitting_ret (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)).
Qed.

Theorem sampling_before_throw_not_erasable (R : realType) :
  ~ (run_exception sample_then_raise ≈ₚ run_exception raises).
Proof.
  intro H.
  pose proof (peutt_hitting_lift H partial_error_hitting
    (@ptree_stable_hitting_ret void1 SubEnumQ MF FI _ _ _ FO _ _ (nat+unit) (inl 7%nat))) as Hlift.
  pose proof (free_omega_qlift_upper_mass R Hlift) as Hmass.
  change ((ratr (2^-1 : rat) : R) * 1 + 0 = 1) in Hmass.
  rewrite mulr1 addr0 in Hmass.
  have Hlt : (ratr (2^-1 : rat) : R) < 1.
  { have H1 : (1 : R) = ratr (1 : rat) by rewrite rmorph1.
    rewrite H1 ltr_rat. native_compute. reflexivity. }
  rewrite Hmass ltxx in Hlt. discriminate.
Qed.

From PTree.Eq.Backend Require Import SubEnumR.

Example real_state_draw_swap (R : realType) {E A X} (mu : SubEnumR R X)
    (k : nat -> X -> ptree (stateE nat +' E) (SubEnumR R) A) s :
  run_state (Vis (inl1 (Get nat)) (fun v => Prob mu (k v))) s ≈ₚ
  run_state (Prob mu (fun x => Vis (inl1 (Get nat)) (fun v => k v x))) s.
Proof. apply run_state_get_prob. Qed.

Section HighCarrier.
Universe hi.
Constraint Set < hi.
Example high_reader (A : Type@{hi}) (k : nat -> nat -> ptree (readerE nat +' void1) SubEnumQ A) env :
  run_reader (Vis (inl1 Ask) (fun x => Vis (inl1 Ask) (k x))) env ≈ₚ
  run_reader (Vis (inl1 Ask) (fun x => k x x)) env.
Proof. apply run_reader_ask_ask. Qed.
End HighCarrier.
