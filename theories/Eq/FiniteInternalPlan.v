Set Universe Polymorphism.
From Coq Require Import Logic.ClassicalChoice Logic.ChoiceFacts
  Logic.FunctionalExtensionality.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import FiniteInternal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Informative witnesses of well-founded compression, indexed by the
    original tree.  These are proof-engineering data, not a new semantics.
    Unlike a bare distribution presentation, a plan retains the actual
    Tau/Prob steps, and stopping never executes Ret or Vis. *)
Section Plans.
Universe node node_rep.
Context {E : Type -> Type} {MN : Type@{node} -> Type@{node_rep}} {R : Type}.
Local Notation tree := (ptree E MN R).

Inductive finite_internal_plan : tree -> Type :=
  | FIPStop t : finite_internal_plan t
  | FIPTau t : finite_internal_plan t -> finite_internal_plan (Tau t)
  | FIPProb {X : Type@{node}} (mu : MN X) (k : X -> tree) :
      (forall x, finite_internal_plan (k x)) -> finite_internal_plan (Prob mu k).

Arguments FIPTau {t} _.
Arguments FIPProb {X} mu {k} _.

Fixpoint internal_plan_path {t} (p : finite_internal_plan t) : Type@{node} :=
  match p with
  | FIPStop _ => unit
  | @FIPTau _ next => internal_plan_path next
  | @FIPProb X mu k next => {x : X & internal_plan_path (next x)}
  end.

Fixpoint internal_plan_residual {t} (p : finite_internal_plan t) :
    internal_plan_path p -> tree :=
  match p as q return internal_plan_path q -> tree with
  | FIPStop t => fun _ => t
  | @FIPTau _ next => @internal_plan_residual _ next
  | @FIPProb X mu k next => fun z => @internal_plan_residual _ (next (projT1 z)) (projT2 z)
  end.
Arguments internal_plan_residual {t} p _.

Fixpoint internal_plan_steps {t} (p : finite_internal_plan t) :
    internal_plan_path p -> nat :=
  match p as q return internal_plan_path q -> nat with
  | FIPStop _ => fun _ => 0
  | @FIPTau _ next => fun z => S (@internal_plan_steps _ next z)
  | @FIPProb X mu k next => fun z => S (@internal_plan_steps _ (next (projT1 z)) (projT2 z))
  end.
Arguments internal_plan_steps {t} p _.

Fixpoint internal_plan_at {t} (p : finite_internal_plan t) :
    nat -> internal_plan_path p -> tree :=
  match p as q in finite_internal_plan s return nat -> internal_plan_path q -> tree with
  | FIPStop t => fun _ _ => t
  | @FIPTau t next => fun n z =>
      match n with 0 => Tau t | S m => @internal_plan_at _ next m z end
  | @FIPProb X mu k next => fun n z =>
      match n with 0 => Prob mu k
      | S m => @internal_plan_at _ (next (projT1 z)) m (projT2 z) end
  end.
Arguments internal_plan_at {t} p _ _.

Lemma internal_plan_at_zero t (p : finite_internal_plan t) z :
  internal_plan_at p 0 z = t.
Proof. destruct p; reflexivity. Qed.

Lemma internal_plan_at_end t (p : finite_internal_plan t) z :
  internal_plan_at p (internal_plan_steps p z) z = internal_plan_residual p z.
Proof.
  induction p as [t|t next IH|X mu k next IH]; cbn in *.
  - reflexivity.
  - apply IH.
  - destruct z as [x z]. apply IH.
Qed.

(** Syntactic execution paths: weights are NOT asserted by this judgment.
    Their distribution is supplied separately by [internal_plan_measure].
    In particular no assertion about the positive mass of an individual
    sample value is made for continuous native backends. *)
Inductive finite_internal_path : tree -> nat -> tree -> Prop :=
  | FIPathStop t : finite_internal_path t 0 t
  | FIPathTau t n u : finite_internal_path t n u ->
      finite_internal_path (Tau t) (S n) u
  | FIPathProb {X} (mu : MN X) (k : X -> tree) x n u :
      finite_internal_path (k x) n u -> finite_internal_path (Prob mu k) (S n) u.

Theorem internal_plan_path_valid t (p : finite_internal_plan t) z :
  finite_internal_path t (internal_plan_steps p z) (internal_plan_residual p z).
Proof.
  induction p as [t|t next IH|X mu k next IH]; cbn in *.
  - constructor.
  - constructor. apply IH.
  - destruct z as [x z]. econstructor. apply IH.
Qed.

Theorem internal_plan_prefix_valid t (p : finite_internal_plan t) z n :
  finite_internal_path t (Nat.min n (internal_plan_steps p z)) (internal_plan_at p n z).
Proof.
  induction p as [t|t next IH|X mu k next IH] in z, n |- *.
  - destruct n; constructor.
  - destruct n; cbn.
    + constructor.
    + constructor. apply IH.
  - destruct z as [x z], n; cbn.
    + constructor.
    + econstructor. apply IH.
Qed.

Theorem internal_plan_suffix_valid t (p : finite_internal_plan t) z n :
  finite_internal_path (internal_plan_at p n z)
    (internal_plan_steps p z - n) (internal_plan_residual p z).
Proof.
  induction p as [t|t next IH|X mu k next IH] in z, n |- *.
  - destruct n; constructor.
  - destruct n; cbn.
    + constructor. apply internal_plan_path_valid.
    + apply IH.
  - destruct z as [x z], n; cbn.
    + econstructor. apply internal_plan_path_valid.
    + apply IH.
Qed.

Context `{NI : SemanticMeasure MN}.

Fixpoint internal_plan_measure {t} (p : finite_internal_plan t) : MN (internal_plan_path p) :=
  match p as q return MN (internal_plan_path q) with
  | FIPStop _ => sem_ret tt
  | @FIPTau _ next => @internal_plan_measure _ next
  | @FIPProb X mu k next => sem_bind mu (fun x =>
      sem_bind (@internal_plan_measure _ (next x))
        (fun z => sem_ret (existT (fun x => internal_plan_path (next x)) x z)))
  end.
Arguments internal_plan_measure {t} p.

Context {MF : Type -> Type} `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}.

Fixpoint internal_plan_frontier {t} (p : finite_internal_plan t) : MF tree :=
  match p with
  | FIPStop t => sem_ret t
  | @FIPTau _ next => internal_plan_frontier next
  | @FIPProb X mu k next => mixed_bind mu (fun x => internal_plan_frontier (next x))
  end.

Theorem internal_plan_frontier_valid t (p : finite_internal_plan t) :
  finite_internal t (internal_plan_frontier p).
Proof.
  induction p; cbn; constructor; assumption.
Qed.

(** Reification uses dependent choice to pick WHOLE typed branch plans.
    It does not pick arbitrary residual values from an AE support fact. *)
Theorem finite_internal_plan_exists t out :
  finite_internal t out ->
  exists p : finite_internal_plan t, internal_plan_frontier p = out.
Proof.
  intro Hcut. induction Hcut as [t|t out Hcut IH|X mu k out Hcut IH].
  - exists (FIPStop t). reflexivity.
  - destruct IH as [p Hp]. exists (FIPTau p). exact Hp.
  - destruct (@non_dep_dep_functional_choice (@choice) X
      (fun x => finite_internal_plan (k x))
      (fun x p => internal_plan_frontier p = out x) IH) as [p Hp].
    exists (FIPProb mu p). cbn. f_equal. apply functional_extensionality. exact Hp.
Qed.
End Plans.

Arguments internal_plan_residual {E MN R t} p _.
Arguments internal_plan_steps {E MN R t} p _.
Arguments internal_plan_at {E MN R t} p _ _.
Arguments internal_plan_measure {E MN R NI t} p.
