(** Reader equations after eliminating Ask; no fictitious Local event. *)
Set Universe Polymorphism.
From ITree.Events Require Import Reader.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Mixed Omega.
From PTree.Eq Require Import PEutt Shallow.
From PTree.Interp Require Import Reader.
From PTree.Interp.Algebra Require Import Computation.
Set Implicit Arguments.
Unset Strict Implicit.

Section Laws.
Context {Env : Type} {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI} `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}.
Local Notation W := (peutt (MF := MF) eq).

Theorem run_reader_ask {A} (k : Env -> ptree (readerE Env +' E) MN A) env :
  W (run_reader (Vis (inl1 Ask) k) env) (run_reader (k env) env).
Proof.
  eapply peutt_tau_step; [unfold run_reader; rewrite observe_interp; reflexivity|].
  apply peutt_observe_eq. rewrite observe_bind. reflexivity.
Qed.

Theorem run_reader_ask_ask {A} (k : Env -> Env -> ptree (readerE Env +' E) MN A) env :
  W (run_reader (Vis (inl1 Ask) (fun x => Vis (inl1 Ask) (k x))) env)
    (run_reader (Vis (inl1 Ask) (fun x => k x x)) env).
Proof.
  eapply peutt_trans with (y := run_reader (k env env) env).
  - eapply peutt_trans; [apply run_reader_ask|apply run_reader_ask].
  - apply peutt_sym. exact (run_reader_ask (fun x => k x x) env).
Qed.

Theorem run_reader_prob {A X} (mu : MN X) (k : X -> ptree (readerE Env +' E) MN A) env :
  W (run_reader (Prob mu k) env) (Prob mu (fun x => run_reader (k x) env)).
Proof. apply peutt_observe_eq. reflexivity. Qed.

Context `{NC : @SemanticMeasureCoreLaws MN NI}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{MO : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.

Theorem run_reader_ask_prob {A X} (mu : MN X)
    (k : Env -> X -> ptree (readerE Env +' E) MN A) env :
  W (run_reader (Vis (inl1 Ask) (fun v => Prob mu (k v))) env)
    (run_reader (Prob mu (fun x => Vis (inl1 Ask) (fun v => k v x))) env).
Proof.
  eapply peutt_trans; [apply run_reader_ask|].
  eapply peutt_trans; [apply run_reader_prob|].
  apply peutt_sym. eapply peutt_trans; [apply run_reader_prob|].
  apply peutt_prob_Proper. intro x. exact (run_reader_ask (fun v => k v x) env).
Qed.
End Laws.
