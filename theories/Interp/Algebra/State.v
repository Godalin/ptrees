(** Global-state equations AFTER interpretation. Source Get/Put remain
    visible events; sampling preserves each branch's current state. *)
Set Universe Polymorphism.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Mixed Omega.
From PTree.Eq Require Import PEutt.
From PTree.Interp Require Import State.
From PTree.Interp.Algebra Require Import Computation.
Set Implicit Arguments.
Unset Strict Implicit.

Section Laws.
Context {S : Type} {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI} `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}.
Local Notation W := (peutt (MF := MF) eq).

Lemma state_get_step {A} (k : S -> ptree (stateE S +' E) MN A) s :
  W (run_state (Vis (inl1 (Get S)) k) s) (run_state (k s) s).
Proof. eapply peutt_tau_step; [rewrite observe_run_state; reflexivity|apply peutt_refl]. Qed.

Lemma state_put_step {A} (k : unit -> ptree (stateE S +' E) MN A) s s' :
  W (run_state (Vis (inl1 (Put S s')) k) s) (run_state (k tt) s').
Proof. eapply peutt_tau_step; [rewrite observe_run_state; reflexivity|apply peutt_refl]. Qed.

Theorem run_state_get_get {A} (k : S -> S -> ptree (stateE S +' E) MN A) s :
  W (run_state (Vis (inl1 (Get S)) (fun x => Vis (inl1 (Get S)) (k x))) s)
    (run_state (Vis (inl1 (Get S)) (fun x => k x x)) s).
Proof.
  eapply peutt_trans with (y := run_state (k s s) s).
  - eapply peutt_trans; [apply state_get_step|apply state_get_step].
  - apply peutt_sym. exact (state_get_step (fun x => k x x) s).
Qed.

Theorem run_state_get_put {A} (k : ptree (stateE S +' E) MN A) s :
  W (run_state (Vis (inl1 (Get S)) (fun x => Vis (inl1 (Put S x)) (fun _ => k))) s)
    (run_state k s).
Proof. eapply peutt_trans; [apply state_get_step|apply state_put_step]. Qed.

Theorem run_state_put_get {A} (k : S -> ptree (stateE S +' E) MN A) s s' :
  W (run_state (Vis (inl1 (Put S s')) (fun _ => Vis (inl1 (Get S)) k)) s)
    (run_state (Vis (inl1 (Put S s')) (fun _ => k s')) s).
Proof.
  eapply peutt_trans with (y := run_state (k s') s').
  - eapply peutt_trans; [apply state_put_step|apply state_get_step].
  - apply peutt_sym. apply state_put_step.
Qed.

Theorem run_state_put_put {A} (k : ptree (stateE S +' E) MN A) s s1 s2 :
  W (run_state (Vis (inl1 (Put S s1)) (fun _ => Vis (inl1 (Put S s2)) (fun _ => k))) s)
    (run_state (Vis (inl1 (Put S s2)) (fun _ => k)) s).
Proof.
  eapply peutt_trans with (y := run_state k s2).
  - eapply peutt_trans; [apply state_put_step|apply state_put_step].
  - apply peutt_sym. apply state_put_step.
Qed.

Theorem run_state_prob {A X} (mu : MN X) (k : X -> ptree (stateE S +' E) MN A) s :
  W (run_state (Prob mu k) s) (Prob mu (fun x => run_state (k x) s)).
Proof. apply peutt_observe_eq. reflexivity. Qed.

Context `{NC : @SemanticMeasureCoreLaws MN NI}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{MO : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.

Theorem run_state_get_prob {A X} (mu : MN X)
    (k : S -> X -> ptree (stateE S +' E) MN A) s :
  W (run_state (Vis (inl1 (Get S)) (fun v => Prob mu (k v))) s)
    (run_state (Prob mu (fun x => Vis (inl1 (Get S)) (fun v => k v x))) s).
Proof.
  eapply peutt_trans; [apply state_get_step|].
  eapply peutt_trans; [apply run_state_prob|].
  apply peutt_sym. eapply peutt_trans; [apply run_state_prob|].
  apply peutt_prob_Proper. intro x. exact (state_get_step (fun v => k v x) s).
Qed.

Theorem run_state_put_prob {A X} (mu : MN X)
    (k : X -> ptree (stateE S +' E) MN A) s s' :
  W (run_state (Vis (inl1 (Put S s')) (fun _ => Prob mu k)) s)
    (run_state (Prob mu (fun x => Vis (inl1 (Put S s')) (fun _ => k x))) s).
Proof.
  eapply peutt_trans; [apply state_put_step|].
  eapply peutt_trans; [apply run_state_prob|].
  apply peutt_sym. eapply peutt_trans; [apply run_state_prob|].
  apply peutt_prob_Proper. intro x. apply state_put_step.
Qed.
End Laws.
