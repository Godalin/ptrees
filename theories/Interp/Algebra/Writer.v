(** Tell-only Writer algebra. The accumulator is always old <> new.
    This exposes the existing State implementation, not a new WriterT. *)
Set Universe Polymorphism.
From ExtLib.Structures Require Import Monoid BinOps.
From ITree.Events Require Import Writer State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Mixed Omega.
From PTree.Eq Require Import PEutt Shallow PStruct.
From PTree.Interp Require Import State Writer StateFacts Structural.
From PTree.Interp.Algebra Require Import Computation.
Set Implicit Arguments.
Unset Strict Implicit.

Definition run_writer_from {W E MN A} (op : Monoid W)
    (t : ptree (writerE W +' E) MN A) (log : W) : ptree E MN (W*A) :=
  run_state (PTree.interp (writer_handler op) t) log.

Section StructuralBind.
Context {W : Type} {E MN : Type -> Type} (op : Monoid W).

Local Lemma state_structural_eq {A} (t u : ptree (stateE W +' E) MN A) log :
  pstruct eq t u -> pstruct eq (run_state t log) (run_state u log).
Proof.
  intro H.
  eapply pstruct_trans; [apply pstruct_sym; apply pstruct_bind_ret_r|].
  eapply pstruct_trans; [|apply pstruct_bind_ret_r].
  eapply pstruct_bind with (RA := state_result_rel eq) (RB := eq).
  - intros [w a] [w' a'] [Hw Ha]. cbn in Hw, Ha. subst. apply pstruct_refl.
  - apply run_state_pstruct. exact H.
Qed.

Theorem run_writer_from_bind {A B} (t : ptree (writerE W +' E) MN A)
    (k : A -> ptree (writerE W +' E) MN B) log :
  pstruct eq (run_writer_from op (PTree.bind t k) log)
    (PTree.bind (run_writer_from op t log)
      (fun wa => run_writer_from op (k (snd wa)) (fst wa))).
Proof.
  unfold run_writer_from. eapply pstruct_trans.
  - apply state_structural_eq. apply pstruct_interp_bind.
  - exact (run_state_bind (PTree.interp (writer_handler op) t)
      (fun a => PTree.interp (writer_handler op) (k a)) log).
Qed.

(** Accumulator-threading bind law of the current implementation. The
    independent WriterT append law is a separate transformer obligation. *)
Theorem run_writer_bind {A B} (t : ptree (writerE W +' E) MN A)
    (k : A -> ptree (writerE W +' E) MN B) :
  pstruct eq (run_writer op (PTree.bind t k))
    (PTree.bind (run_writer op t)
      (fun wa => run_writer_from op (k (snd wa)) (fst wa))).
Proof. apply run_writer_from_bind. Qed.
End StructuralBind.

Section Laws.
Context {W : Type} {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI} `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}.
Variable op : Monoid W.
Local Notation B := (peutt (MF := MF) eq).

Theorem run_writer_from_tell {A} w (k : unit -> ptree (writerE W +' E) MN A) log :
  B (run_writer_from op (Vis (inl1 (Tell w)) k) log)
    (run_writer_from op (k tt) (monoid_plus op log w)).
Proof.
  unfold run_writer_from.
  eapply peutt_tau_step.
  - rewrite observe_run_state, observe_interp. reflexivity.
  - eapply peutt_tau_step.
    + rewrite observe_run_state, observe_bind. reflexivity.
    + eapply peutt_tau_step.
      * rewrite observe_run_state, observe_bind. reflexivity.
      * apply peutt_observe_eq. rewrite !observe_run_state, observe_bind. reflexivity.
Qed.

Theorem run_writer_from_prob {A X} (mu : MN X)
    (k : X -> ptree (writerE W +' E) MN A) log :
  B (run_writer_from op (Prob mu k) log)
    (Prob mu (fun x => run_writer_from op (k x) log)).
Proof. apply peutt_observe_eq. reflexivity. Qed.

Theorem run_writer_prob {A X} (mu : MN X) (k : X -> ptree (writerE W +' E) MN A) :
  B (run_writer op (Prob mu k)) (Prob mu (fun x => run_writer op (k x))).
Proof. apply run_writer_from_prob. Qed.

Context `{L : MonoidLaws W op}.

Theorem run_writer_tell_unit {A} (k : ptree (writerE W +' E) MN A) :
  B (run_writer op (Vis (inl1 (Tell (monoid_unit op))) (fun _ => k))) (run_writer op k).
Proof.
  change (B (run_writer_from op (Vis (inl1 (Tell (monoid_unit op))) (fun _ => k)) (monoid_unit op))
    (run_writer_from op k (monoid_unit op))).
  eapply peutt_trans; [apply run_writer_from_tell|].
  rewrite monoid_lunit. apply peutt_refl.
Qed.

Theorem run_writer_from_tell_append {A} w1 w2 (k : ptree (writerE W +' E) MN A) log :
  B (run_writer_from op (Vis (inl1 (Tell w1)) (fun _ => Vis (inl1 (Tell w2)) (fun _ => k))) log)
    (run_writer_from op (Vis (inl1 (Tell (monoid_plus op w1 w2))) (fun _ => k)) log).
Proof.
  eapply peutt_trans with (y := run_writer_from op k (monoid_plus op (monoid_plus op log w1) w2)).
  - eapply peutt_trans; [apply run_writer_from_tell|apply run_writer_from_tell].
  - rewrite monoid_assoc. apply peutt_sym. apply run_writer_from_tell.
Qed.

Theorem run_writer_tell_append {A} w1 w2 (k : ptree (writerE W +' E) MN A) :
  B (run_writer op (Vis (inl1 (Tell w1)) (fun _ => Vis (inl1 (Tell w2)) (fun _ => k))))
    (run_writer op (Vis (inl1 (Tell (monoid_plus op w1 w2))) (fun _ => k))).
Proof. apply run_writer_from_tell_append. Qed.

Context `{NC : @SemanticMeasureCoreLaws MN NI}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{MO : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.

Theorem run_writer_tell_prob {A X} w (mu : MN X)
    (k : X -> ptree (writerE W +' E) MN A) :
  B (run_writer op (Vis (inl1 (Tell w)) (fun _ => Prob mu k)))
    (run_writer op (Prob mu (fun x => Vis (inl1 (Tell w)) (fun _ => k x)))).
Proof.
  change (B (run_writer_from op (Vis (inl1 (Tell w)) (fun _ => Prob mu k)) (monoid_unit op))
    (run_writer_from op (Prob mu (fun x => Vis (inl1 (Tell w)) (fun _ => k x))) (monoid_unit op))).
  eapply peutt_trans; [apply run_writer_from_tell|].
  eapply peutt_trans; [apply run_writer_from_prob|].
  apply peutt_sym. eapply peutt_trans; [apply run_writer_from_prob|].
  apply peutt_prob_Proper. intro x. apply run_writer_from_tell.
Qed.
End Laws.
