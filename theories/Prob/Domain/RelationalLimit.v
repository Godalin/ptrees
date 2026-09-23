(** Relational continuity in the independent expectation domain.
    Dual constraints are closed under pointwise suprema without any support
    restriction. Joint existence is a separate transport theorem. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype choice ssrnat ssralg ssrnum order reals boolp.
From PTree.Prob.Domain Require Import Expectation Countable Coupling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Limits.
Variable R : realType.

Theorem oval_dual_lub {A B} (T : A -> B -> Prop)
    (c : nat -> OmegaVal R A) (d : nat -> OmegaVal R B)
    (Hc : oval_increasing c) (Hd : oval_increasing d) :
  (forall n, oval_dual T (c n) (d n)) ->
  oval_dual T (oval_lub Hc) (oval_lub Hd).
Proof.
  intros H f g Hf Hg Hfg.
  change (oval_sup (fun n => oval_eval (c n) f) <=
          oval_sup (fun n => oval_eval (d n) g)).
  apply (oval_sup_mono (fun n => proj2 (oval_eval_bounds (d n) Hg))).
  intro n; exact (H n f g Hf Hg Hfg).
Qed.

Theorem oval_bidual_lub {A B} (T : A -> B -> Prop)
    (c : nat -> OmegaVal R A) (d : nat -> OmegaVal R B)
    (Hc : oval_increasing c) (Hd : oval_increasing d) :
  (forall n, oval_bidual T (c n) (d n)) ->
  oval_bidual T (oval_lub Hc) (oval_lub Hd).
Proof.
  intro H; split; apply oval_dual_lub; intro n;
    [exact (proj1 (H n))|exact (proj2 (H n))].
Qed.

Lemma oval_ae_lub {A} (c : nat -> OmegaVal R A)
    (Hc : oval_increasing c) P :
  (forall n, oval_ae (c n) P) -> oval_ae (oval_lub Hc) P.
Proof.
  intros H f g Hf Hg Hfg; apply oval_sup_ext=> n.
  exact (H n f g Hf Hg Hfg).
Qed.

(** The covers may grow with n, repeat entries, and contain invalid codes.
    Countability is a property of the measures, not of the ambient Type. *)
Theorem oval_countably_supported_lub {A} (c : nat -> OmegaVal R A)
    (Hc : oval_increasing c) :
  (forall n, oval_countably_supported (c n)) ->
  oval_countably_supported (oval_lub Hc).
Proof.
  intro H.
  pose e n := proj1_sig (cid (H n)).
  pose cover k := match (@unpickle _ k : option (nat * nat)) with
    | Some (i,j) => e i j | None => None end.
  exists cover; apply oval_ae_lub=> n.
  apply (@oval_ae_mono R A (c n) (oval_enumerated (e n))).
  - exact (proj2_sig (cid (H n))).
  - intros x [j Hj]; exists (pickle (n,j)).
    rewrite /cover pickleK; exact Hj.
Qed.
End Limits.
