(** Reader and Writer are clients of the completed generic handler/State
    proofs. Neither introduces its own coinduction or backend-specific law. *)
Set Universe Polymorphism.
From ExtLib.Structures Require Import Monoid.
From ITree.Events Require Import Reader Writer.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder RelationalClosure.
From PTree.Eq Require Import PStruct PEutt.
From PTree.Interp Require Import Reader Writer State Structural Unrestricted StatePreservation.
Set Implicit Arguments.
Unset Strict Implicit.

Lemma run_reader_ret {Env E MN A} (a : A) env :
  pstruct eq (@run_reader Env E MN A (Ret a) env) (Ret a).
Proof. apply observe_eq_pstruct. reflexivity. Qed.

Lemma run_reader_bind {Env E MN A B} env (t : ptree (readerE Env +' E) MN A)
    (k : A -> ptree (readerE Env +' E) MN B) :
  pstruct eq (run_reader (PTree.bind t k) env)
    (PTree.bind (run_reader t env) (fun a => run_reader (k a) env)).
Proof. apply pstruct_interp_bind. Qed.

Lemma run_writer_ret {W E MN A} (op : Monoid W) (a : A) :
  pstruct eq (@run_writer W E MN A op (Ret a)) (Ret (monoid_unit op,a)).
Proof. apply observe_eq_pstruct. reflexivity. Qed.

Section Behavior.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{BindOrd : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MixedOrd : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variable Hzero : relational_zero FO.
Variable Hlimit : relational_lub FO.

Theorem run_reader_peutt {Env A B} (RR : A -> B -> Prop) env
    (t : ptree (readerE Env +' E) MN A) (u : ptree (readerE Env +' E) MN B) :
  @peutt (readerE Env +' E) MN MF FI FC MX FO A B RR t u ->
  @peutt E MN MF FI FC MX FO A B RR (run_reader t env) (run_reader u env).
Proof. apply (Unrestricted.peutt_interp Hzero Hlimit). Qed.

Theorem run_writer_peutt {W A B} (op : Monoid W) (RR : A -> B -> Prop)
    (t : ptree (writerE W +' E) MN A) (u : ptree (writerE W +' E) MN B) :
  @peutt (writerE W +' E) MN MF FI FC MX FO A B RR t u ->
  @peutt E MN MF FI FC MX FO (W*A) (W*B) (state_result_rel RR)
    (run_writer op t) (run_writer op u).
Proof.
  intro H. apply (StatePreservation.run_state_peutt (relational_bind_of_laws FB) Hzero Hlimit).
  exact (Unrestricted.peutt_interp Hzero Hlimit (writer_handler op) H).
Qed.
End Behavior.
