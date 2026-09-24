(** Structural laws for the actual ITree datatype embedding. No probability
    interpretation is selected; sampling elaboration reuses PTree interp. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Program Require Import Equality.
From Coinduction Require Import all.
From ITree.Core Require Import ITreeDefinition.
From ITree.Indexed Require Import Sum.
From ITree.Eq Require Import Eqit Shallow.
From PTree.Core Require Import PTreeDefinition ITreeBridge.
From PTree.Eq Require Import Shallow PStruct.
From PTree.Interp Require Import Structural.
Set Implicit Arguments.
Unset Strict Implicit.
Notation "` R" := (elem R) (at level 10).

Section Embedding.
Context {E MN : Type -> Type}.
Lemma from_itree_ret {A} (a : A) :
  pstruct eq (@from_itree E MN A (ITreeDefinition.Ret a)) (Ret a).
Proof. apply observe_eq_pstruct. reflexivity. Qed.
Lemma from_itree_tau {A} (t : itree E A) :
  pstruct eq (@from_itree E MN A (ITreeDefinition.Tau t)) (Tau (from_itree t)).
Proof. apply observe_eq_pstruct. reflexivity. Qed.
Lemma from_itree_vis {A X} (e : E X) (k : X -> itree E A) :
  pstruct eq (@from_itree E MN A (ITreeDefinition.Vis e k))
    (Vis e (fun x => from_itree (k x))).
Proof. apply observe_eq_pstruct. reflexivity. Qed.

Definition from_itree_bind_candidate {A B} (t u : ptree E MN B) : Prop :=
  (exists (s : itree E A) (k : A -> itree E B),
    t = from_itree (ITree.bind s k) /\
    u = PTree.bind (from_itree s) (fun x => from_itree (k x))) \/ pstruct eq t u.

Theorem from_itree_bind {A B} (t : itree E A) (k : A -> itree E B) :
  pstruct eq (@from_itree E MN B (ITree.bind t k))
    (PTree.bind (from_itree t) (fun x => from_itree (k x))).
Proof.
  assert (H : forall u v, @from_itree_bind_candidate A B u v -> pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v [[s [c [-> ->]]]|Hdone].
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (from_itree (ITree.bind s c)))
        (observe (PTree.bind (from_itree s) (fun x => from_itree (c x))))).
      rewrite observe_from_itree, ITree.Eq.Shallow.observe_bind, PTree.Eq.Shallow.observe_bind.
      try rewrite observe_from_itree.
      destruct (ITreeDefinition.observe s) as [a|s'|X e d]; cbn.
      + rewrite <- observe_from_itree.
        eapply pstructF_monotone; [|apply pstruct_unfold; apply pstruct_refl].
        intros u v Huv. apply CIH. right. exact Huv.
      + constructor. apply CIH. left. exists s', c. split; reflexivity.
      + constructor. intro x. apply CIH. left. exists (d x), c. split; reflexivity.
    - unfold pstruct_body. eapply pstructF_monotone; [|exact (pstruct_unfold Hdone)].
      intros u' v' Huv. apply CIH. right. exact Huv. }
  apply H. left. exists t, k. split; reflexivity.
Qed.

Section Iteration.
Context {I A : Type} (step : I -> itree E (I+A)).
Local Definition left_cont (v : I+A) : itree E A :=
  match v with inl i => ITreeDefinition.Tau (ITree.iter step i)
  | inr a => ITreeDefinition.Ret a end.
Local Definition right_cont (v : I+A) : ptree E MN A :=
  match v with inl i => Tau (PTree.iter (fun j => from_itree (step j)) i)
  | inr a => Ret a end.
Inductive from_itree_iter_candidate : ptree E MN A -> ptree E MN A -> Prop :=
| IterMain i : from_itree_iter_candidate
    (from_itree (ITree.iter step i)) (PTree.iter (fun j => from_itree (step j)) i)
| IterBind s : from_itree_iter_candidate
    (from_itree (ITree.bind s left_cont))
    (PTree.bind (from_itree s) right_cont).

Theorem from_itree_iter i :
  pstruct eq (@from_itree E MN A (ITree.iter step i))
    (PTree.iter (fun j => from_itree (step j)) i).
Proof.
  assert (H : forall u v, from_itree_iter_candidate u v -> pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Huv. destruct Huv as [j|s].
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (from_itree (ITree.bind (step j) left_cont)))
        (observe (PTree.bind (from_itree (step j)) right_cont))).
      rewrite observe_from_itree, ITree.Eq.Shallow.observe_bind, PTree.Eq.Shallow.observe_bind.
      try rewrite observe_from_itree.
      destruct (ITreeDefinition.observe (step j)) as [[j'|a]|s'|X e d]; cbn.
      + constructor. apply CIH. constructor.
      + constructor. reflexivity.
      + constructor. apply CIH. constructor.
      + constructor. intro x. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (from_itree (ITree.bind s left_cont)))
        (observe (PTree.bind (from_itree s) right_cont))).
      rewrite observe_from_itree, ITree.Eq.Shallow.observe_bind, PTree.Eq.Shallow.observe_bind.
      try rewrite observe_from_itree.
      destruct (ITreeDefinition.observe s) as [[j'|a]|s'|X e d]; cbn.
      + constructor. apply CIH. constructor.
      + constructor. reflexivity.
      + constructor. apply CIH. constructor.
      + constructor. intro x. apply CIH. constructor. }
  apply H. constructor.
Qed.
End Iteration.
End Embedding.

Section Interpreting.
Context {E F MN : Type -> Type} (h : Handler.Handler MN E F).
Lemma interp_itree_ret {A} (a : A) :
  pstruct eq (interp_itree h (ITreeDefinition.Ret a)) (Ret a).
Proof. apply observe_eq_pstruct. reflexivity. Qed.

Lemma interp_itree_tau {A} (t : itree E A) :
  pstruct eq (interp_itree h (ITreeDefinition.Tau t)) (Tau (interp_itree h t)).
Proof. apply observe_eq_pstruct. reflexivity. Qed.

Lemma interp_itree_vis {A X} (e : E X) (k : X -> itree E A) :
  pstruct eq (interp_itree h (ITreeDefinition.Vis e k))
    (Tau (PTree.bind (h e) (fun x => interp_itree h (k x)))).
Proof. apply observe_eq_pstruct. reflexivity. Qed.

Theorem interp_itree_bind {A B} (t : itree E A) (k : A -> itree E B) :
  pstruct eq (interp_itree h (ITree.bind t k))
    (PTree.bind (interp_itree h t) (fun x => interp_itree h (k x))).
Proof.
  unfold interp_itree. eapply pstruct_trans.
  - apply pstruct_interp. apply from_itree_bind.
  - apply pstruct_interp_bind.
Qed.

Theorem interp_itree_iter {I A} (step : I -> itree E (I+A)) i :
  pstruct eq (interp_itree h (ITree.iter step i))
    (PTree.iter (fun j => interp_itree h (step j)) i).
Proof.
  unfold interp_itree. eapply pstruct_trans.
  - apply pstruct_interp. apply from_itree_iter.
  - apply pstruct_interp_iter.
Qed.
End Interpreting.

Theorem interp_itree_postcompose {E F G MN A}
    (h : Handler.Handler MN E F) (g : Handler.Handler MN F G) (t : itree E A) :
  pstruct eq (PTree.interp g (interp_itree h t))
    (interp_itree (Handler.cat h g) t).
Proof. apply pstruct_interp_compose. Qed.

(** The weak law removes exactly this administrative Tau. *)
Lemma elaborate_sample_structural {MN E A X} (mu : MN X)
    (k : X -> itree (probE MN +' E) A) :
  pstruct eq (elaborate (ITreeDefinition.Vis (inl1 (Sample mu)) k))
    (Tau (Prob mu (fun x => elaborate (k x)))).
Proof.
  eapply pstruct_trans; [apply interp_itree_vis|].
  apply pstruct_fold. constructor.
  apply pstruct_fold. rewrite PTree.Eq.Shallow.observe_bind. cbn.
  constructor. intro x. apply observe_eq_pstruct.
  rewrite PTree.Eq.Shallow.observe_bind. reflexivity.
Qed.

Lemma elaborate_vis_structural {MN E A X} (e : E X)
    (k : X -> itree (probE MN +' E) A) :
  pstruct eq (elaborate (ITreeDefinition.Vis (inr1 e) k))
    (Tau (Vis e (fun x => elaborate (k x)))).
Proof.
  eapply pstruct_trans; [apply interp_itree_vis|].
  apply pstruct_fold. constructor.
  apply pstruct_fold. rewrite PTree.Eq.Shallow.observe_bind. cbn.
  constructor. intro x. apply observe_eq_pstruct.
  rewrite PTree.Eq.Shallow.observe_bind. reflexivity.
Qed.

Lemma interp_itree_trigger_structural {E F MN X}
    (h : Handler.Handler MN E F) (e : E X) :
  pstruct eq (interp_itree h (ITree.trigger e)) (Tau (h X e)).
Proof.
  eapply pstruct_trans; [apply interp_itree_vis|].
  apply pstruct_fold. constructor.
  eapply pstruct_trans with (y := PTree.bind (h X e) (fun x => Ret x)).
  - eapply pstruct_bind with (RA := eq) (RB := eq).
    + intros x y ->. apply interp_itree_ret.
    + apply pstruct_refl.
  - apply pstruct_bind_ret_r.
Qed.
