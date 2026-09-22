(** Role: Native-parametric external validation of observation certificates.
    Assumptions concern only the interpretation of native operations. In
    particular, a native lub is used only on an increasing interpreted chain;
    no native omega-completeness or FreeOmega soundness is assumed. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure Omega.
From PTree.Prob.Domain Require Import Expectation.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation
  PTree.Prob.FreeOmega.Observation.
From PTree.Prob.FreeOmega.Validation Require Import Expectation Continuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Observation.
Context {MN : Type -> Type} {R : realType}.
Context `{NI : SemanticMeasure MN} `{NO : @SemanticOmega MN NI}.
Variable native : forall X, MN X -> OmegaVal R X.
Arguments native {X} _.
Hypothesis native_ret : forall X (x : X), oval_eq (native (sem_ret x)) (oval_ret R x).
Hypothesis native_zero : forall X, oval_eq (native (@sem_zero MN NI NO X)) (@oval_bottom R X).
Hypothesis native_bind : forall X Y (mu : MN X) (k : X -> MN Y),
  oval_eq (native (sem_bind mu k)) (oval_bind (native mu) (fun x => native (k x))).
Hypothesis native_lift : forall X Y (T : X -> Y -> Prop) (mu : MN X) (nu : MN Y) f g,
  sem_lift T mu nu -> oval_test f -> oval_test g ->
  (forall x y, T x y -> f x <= g y) -> oval_eval (native mu) f <= oval_eval (native nu) g.
Hypothesis native_lub : forall X (c : nat -> MN X) out,
  (forall n f, oval_test f -> oval_eval (native (c n)) f <= oval_eval (native (c (S n))) f) ->
  sem_lub c out -> forall f, oval_test f ->
  oval_sup (fun n => oval_eval (native (c n)) f) = oval_eval (native out) f.
Local Notation upper := (free_omega_model_upper (@native)).

Theorem model_observes_upper {A O} (obs : A -> O) t out f :
  free_omega_observes obs t out -> oval_test f ->
  upper t (fun x => f (obs x)) = oval_eval (native out) f.
Proof.
  intro H; revert f; induction H; intros f Hf; cbn [free_omega_model_upper].
  - symmetry; exact (native_ret (obs x) Hf).
  - symmetry; exact (native_zero Hf).
  - rewrite (native_bind mu front Hf).
    change (oval_eval (native mu) (fun x => upper (k x) (fun y => f (obs y))) =
      oval_eval (native mu) (fun x => oval_eval (native (front x)) f)).
    apply oval_eval_ext=> x; exact (H0 x f Hf).
  - rewrite (functional_extensionality _ _ (fun n => H0 n f Hf)).
    apply native_lub; [|exact H1|exact Hf].
    intros n g Hg.
    rewrite -(H0 n g Hg) -(H0 (S n) g Hg).
    exact (model_approx_mono native_lift (H2 n) (fun x => Hg (obs x))).
Qed.
End Observation.
