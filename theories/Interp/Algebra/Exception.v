(** Early exit is a returned error, not probability loss. No rule here
    discards a preceding sample: its missing mass must be retained. *)
Set Universe Polymorphism.
From Coinduction Require Import all.
From ITree.Events Require Import Exception.
From ITree.Basics Require Import Basics.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Mixed Omega.
From PTree.Eq Require Import PEutt PStruct Shallow.
From PTree.Interp Require Import Exception.
From PTree.Interp.Algebra Require Import Computation.
Set Implicit Arguments.
Unset Strict Implicit.
Notation "` R" := (elem R) (at level 10).

Section StructuralBind.
Context {Err : Type} {E MN : Type -> Type} {A B : Type}.
Variable k : A -> ptree (exceptE Err +' E) MN B.
Definition exception_bind_cont (v : Err+A) : ptree E MN (Err+B) :=
  match v with inl err => Ret (inl err) | inr a => run_exception (k a) end.
Definition exception_bind_candidate (u v : ptree E MN (Err+B)) : Prop :=
  (exists t, u = run_exception (PTree.bind t k) /\
    v = PTree.bind (run_exception t) exception_bind_cont) \/ pstruct eq u v.

Theorem run_exception_bind (t : ptree (exceptE Err +' E) MN A) :
  pstruct eq (run_exception (PTree.bind t k))
    (PTree.bind (run_exception t) exception_bind_cont).
Proof.
  assert (H : forall u v, exception_bind_candidate u v -> pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v [[s [-> ->]]|Hdone].
    - unfold pstruct_body.
      change (pstructF eq (` CH) (observe (run_exception (PTree.bind s k)))
        (observe (PTree.bind (run_exception s) exception_bind_cont))).
      rewrite observe_run_exception, !observe_bind, observe_run_exception.
      destruct (observe s) as [a|s'|X e c|X mu c]; cbn.
      + rewrite <- observe_run_exception.
        eapply pstructF_monotone; [|apply pstruct_unfold; apply pstruct_refl].
        intros u' v' Huv. apply CIH. right. exact Huv.
      + constructor. apply CIH. left. exists s'. split; reflexivity.
      + destruct e as [ex|fe]; cbn [exception_bind_cont].
        * constructor. reflexivity.
        * constructor. intro x. apply CIH. left. exists (c x). split; reflexivity.
      + constructor. intro x. apply CIH. left. exists (c x). split; reflexivity.
    - unfold pstruct_body. eapply pstructF_monotone; [|exact (pstruct_unfold Hdone)].
      intros u' v' Huv. apply CIH. right. exact Huv. }
  apply H. left. exists t. split; reflexivity.
Qed.
End StructuralBind.

Section Laws.
Context {Err : Type} {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}.
Local Notation W := (peutt (MF := MF) eq).

Theorem run_exception_ret {A} (a : A) :
  W (@run_exception Err E MN A (Ret a)) (Ret (inr a)).
Proof. apply peutt_observe_eq. reflexivity. Qed.

Theorem run_exception_throw {A} (err : Err) :
  W (@run_exception Err E MN A (Vis (inl1 (Throw err)) (fun v : void => match v with end)))
    (Ret (inl err)).
Proof. apply peutt_observe_eq. reflexivity. Qed.

Theorem run_exception_throw_bind {A B} (err : Err)
    (k : A -> ptree (exceptE Err +' E) MN B) :
  W (run_exception (PTree.bind (Vis (inl1 (Throw err)) (fun v : void => match v with end)) k))
    (Ret (inl err)).
Proof. apply peutt_observe_eq. rewrite observe_run_exception, observe_bind. reflexivity. Qed.

Theorem run_exception_prob {A X} (mu : MN X) (k : X -> ptree (exceptE Err +' E) MN A) :
  W (run_exception (Prob mu k)) (Prob mu (fun x => run_exception (k x))).
Proof. apply peutt_observe_eq. reflexivity. Qed.
End Laws.
