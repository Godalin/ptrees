(** Proof-only reconciliation of ITree's post-handler Tau with PTree's
    pre-handler Tau. This is a source-interpreter square, not postcomposition
    of two PTree handlers. No restriction is imposed on the source handler. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import RelationClasses Morphisms.
From Paco Require Import paco.
From Coinduction Require Import all.
From ITree.Core Require Import ITreeDefinition KTreeFacts.
From ITree.Eq Require Import Eqit Shallow UpToTaus Paco2.
From ITree.Interp Require Import Interp InterpFacts.
From PTree.Core Require Import PTreeDefinition ITreeBridge.
From PTree.Eq Require Import PStruct Shallow.
From PTree.Interp Require Import ITreeStructural.
Set Implicit Arguments.
Unset Strict Implicit.
Notation "` R" := (elem R) (at level 10).

Section Source.
Context {E F : Type -> Type} (h : forall X, E X -> itree F X).

(** An auxiliary scheduling variant; it is not an alternative public
    elaborator. Both interpreters use the original handler unchanged. *)
CoFixpoint itree_interp_before {A} (t : itree E A) : itree F A :=
  match ITreeDefinition.observe t with
  | ITreeDefinition.RetF a => ITreeDefinition.Ret a
  | ITreeDefinition.TauF u => ITreeDefinition.Tau (itree_interp_before u)
  | @ITreeDefinition.VisF _ _ _ X e k =>
      ITreeDefinition.Tau (ITree.bind (@h X e) (fun x => itree_interp_before (k x)))
  end.

Lemma itree_interp_before_unfold {A} (t : itree E A) :
  eq_itree eq (itree_interp_before t)
    (match ITreeDefinition.observe t with
    | ITreeDefinition.RetF a => ITreeDefinition.Ret a
    | ITreeDefinition.TauF u => ITreeDefinition.Tau (itree_interp_before u)
    | @ITreeDefinition.VisF _ _ _ X e k =>
        ITreeDefinition.Tau (ITree.bind (@h X e) (fun x => itree_interp_before (k x)))
    end).
Proof.
  apply observing_sub_eqit. constructor.
  unfold ITreeDefinition.observe. cbn. unfold ITreeDefinition.observe.
  destruct (ITreeDefinition._observe t); reflexivity.
Qed.

Definition itree_interp_schedule_candidate {A} (l r : itree F A) : Prop :=
  (exists t, l = itree_interp_before t /\ r = Interp.interp h t) \/
  (exists X (active : itree F X) (k : X -> itree E A),
    l = ITreeDefinition.Tau (ITree.bind active (fun x => itree_interp_before (k x))) /\
    r = ITree.bind active (fun x => ITreeDefinition.Tau (Interp.interp h (k x)))).

Lemma itree_interp_schedule {A} : forall l r : itree F A,
  itree_interp_schedule_candidate l r -> eutt eq l r.
Proof.
  einit. ecofix CIH. intros l r Hlr.
  destruct Hlr as [[t [-> ->]]|[X [active [k [-> ->]]]]].
  - rewrite itree_interp_before_unfold, unfold_interp.
    destruct (ITreeDefinition.observe t) as [a|u|X e k]; cbn.
    + apply reflexivity.
    + etau. ebase. right. apply CIHL. left. exists u. split; reflexivity.
    + remember (@h X e) as active. clear Heqactive.
      rewrite (itree_eta active). destruct (ITreeDefinition.observe active) as [x|a|Y e' c]; cbn.
      * rewrite !bind_ret_l. etau. ebase. right. apply CIHL.
        left. exists (k x). split; reflexivity.
      * rewrite !bind_tau. etau. ebase. right. apply CIHL.
        right. exists X, a, k. split; reflexivity.
      * rewrite !bind_vis, tau_euttge. evis. intro y.
        rewrite <- (tau_eutt (ITree.bind (c y) (fun x => itree_interp_before (k x)))).
        ebase. right. apply CIHH. right. exists X, (c y), k. split; reflexivity.
  - rewrite (itree_eta active). destruct (ITreeDefinition.observe active) as [x|a|Y e c]; cbn.
    + rewrite !bind_ret_l. etau. ebase. right. apply CIHL.
      left. exists (k x). split; reflexivity.
    + rewrite !bind_tau. etau. ebase. right. apply CIHL.
      right. exists X, a, k. split; reflexivity.
    + rewrite !bind_vis, tau_euttge. evis. intro y.
      rewrite <- (tau_eutt (ITree.bind (c y) (fun x => itree_interp_before (k x)))).
      ebase. right. apply CIHH. right. exists X, (c y), k. split; reflexivity.
Qed.

Theorem itree_interp_before_eutt {A} (t : itree E A) :
  eutt eq (itree_interp_before t) (Interp.interp h t).
Proof. apply itree_interp_schedule. left. exists t. split; reflexivity. Qed.

Section Embedding.
Context {MN : Type -> Type} {A : Type}.
Local Definition lifted_handler X (e : E X) : ptree F MN X := from_itree (h e).

Lemma observe_embed_before (t : itree E A) :
  observe (@from_itree F MN A (itree_interp_before t)) =
  match ITreeDefinition.observe t with
  | ITreeDefinition.RetF a => RetF a
  | ITreeDefinition.TauF u => TauF (from_itree (itree_interp_before u))
  | @ITreeDefinition.VisF _ _ _ X e k =>
      TauF (from_itree (ITree.bind (h e) (fun x => itree_interp_before (k x))))
  end.
Proof.
  rewrite observe_from_itree. unfold ITreeDefinition.observe at 1. cbn.
  destruct (ITreeDefinition.observe t); reflexivity.
Qed.

Definition embed_interp_candidate (l r : ptree F MN A) : Prop :=
  (exists t, l = from_itree (itree_interp_before t) /\
    r = PTree.interp lifted_handler (from_itree t)) \/
  (exists X (active : itree F X) (k : X -> itree E A),
    l = from_itree (ITree.bind active (fun x => itree_interp_before (k x))) /\
    r = PTree.bind (from_itree active)
      (fun x => PTree.interp lifted_handler (from_itree (k x)))).

Theorem from_itree_interp_before (t : itree E A) :
  pstruct eq (from_itree (itree_interp_before t))
    (PTree.interp lifted_handler (from_itree t)).
Proof.
  assert (H : forall l r, embed_interp_candidate l r -> pstruct eq l r).
  { unfold pstruct. coinduction CH CIH. intros l r Hlr.
    unfold pstruct_body.
    destruct Hlr as [[s [-> ->]]|[X [active [k [-> ->]]]]].
    - change (pstructF eq (` CH) (observe (from_itree (itree_interp_before s)))
        (observe (PTree.interp lifted_handler (from_itree s)))).
      rewrite observe_embed_before, observe_interp, observe_from_itree.
      destruct (ITreeDefinition.observe s) as [a|u|Y e c]; cbn.
      + constructor. reflexivity.
      + constructor. apply CIH. left. exists u. split; reflexivity.
      + constructor. apply CIH. right. exists Y, (h e), c. split; reflexivity.
    - change (pstructF eq (` CH)
        (observe (from_itree (ITree.bind active (fun x => itree_interp_before (k x)))))
        (observe (PTree.bind (from_itree active)
          (fun x => PTree.interp lifted_handler (from_itree (k x)))))).
      rewrite observe_from_itree, ITree.Eq.Shallow.observe_bind,
        PTree.Eq.Shallow.observe_bind, observe_from_itree.
      destruct (ITreeDefinition.observe active) as [x|u|Y e c]; cbn.
      + rewrite <- observe_from_itree, observe_embed_before,
          observe_interp, observe_from_itree.
        destruct (ITreeDefinition.observe (k x)) as [a|v|Z e' d]; cbn.
        * constructor. reflexivity.
        * constructor. apply CIH. left. exists v. split; reflexivity.
        * constructor. apply CIH. right. exists Z, (h e'), d. split; reflexivity.
      + constructor. apply CIH. right. exists X, u, k. split; reflexivity.
      + constructor. intro y. apply CIH. right. exists X, (c y), k. split; reflexivity. }
  apply H. left. exists t. split; reflexivity.
Qed.
End Embedding.
End Source.
