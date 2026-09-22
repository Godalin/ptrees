(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order rat reals.
From mathcomp.classical Require Import classical_sets.
From mathcomp.analysis Require Import ereal.
Require Import PTree.Prob.Backend.Common.RatSubTypes PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Iteration PTree.Prob.Backend.EnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ RatSubTypes GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Internal scalar model for the raw weighted EnumQ backend.  Unlike the
    SubEnumQ model, neither total mass nor intermediate upper expectations
    have a uniform finite bound.  Supremum is therefore taken in extended
    reals.  Arbitrary formal Lub nodes still need not be additive measures.
    This file alone does NOT prove preservation by quotient coupling. *)
Section ExtendedUpper.
Variable R : realType.

Fixpoint enumQ_extended_expect {A} (f : A -> \bar R) (mu : EnumQ A) : \bar R :=
  match mu with
  | nil => 0
  | (p, x) :: tail => (ratr (Qval p))%:E * f x + enumQ_extended_expect f tail
  end.

Lemma enumQ_extended_expect_nonnegative {A} (f : A -> \bar R) mu :
  (forall x, 0 <= f x) -> 0 <= enumQ_extended_expect f mu.
Proof.
  move=> Hf. elim: mu=> [|[p x] tail IH] /=; first exact: lexx.
  apply: adde_ge0 IH. apply: mule_ge0 (Hf x).
  by rewrite lee_fin ler0q; apply: le_nnQ0.
Qed.

Lemma enumQ_extended_expect_mono {A} (f g : A -> \bar R) mu :
  (forall x, f x <= g x) -> enumQ_extended_expect f mu <= enumQ_extended_expect g mu.
Proof.
  move=> Hfg. elim: mu=> [|[p x] tail IH] /=; first exact: lexx.
  apply: leeD IH. apply: lee_wpmul2l (Hfg x).
  by rewrite lee_fin ler0q; apply: le_nnQ0.
Qed.

Lemma enumQ_extended_expect_zero {A} (mu : EnumQ A) :
  enumQ_extended_expect (fun _ => 0) mu = 0.
Proof. by elim: mu=> [|[p x] tail IH] //=; rewrite mule0 IH adde0. Qed.

Lemma enumQ_extended_expect_app {A} (f : A -> \bar R) mu nu :
  enumQ_extended_expect f (mu ++ nu) = enumQ_extended_expect f mu + enumQ_extended_expect f nu.
Proof. by elim: mu=> [|[p x] tail IH] /=; rewrite ?add0e ?IH ?addeA. Qed.

Lemma enumQ_extended_expect_scale {A} (f : A -> \bar R) p mu :
  (forall x, 0 <= f x) ->
  enumQ_extended_expect f (scale_EnumQ p mu) =
    (ratr (Qval p))%:E * enumQ_extended_expect f mu.
Proof.
  move=> Hf. elim: mu=> [|[q x] tail IH] /=; first by rewrite mule0.
  rewrite IH ge0_muleDr; last 2 first.
  - apply mule_ge0; [|exact: Hf]. by rewrite lee_fin ler0q; apply: le_nnQ0.
  - exact: enumQ_extended_expect_nonnegative.
  congr (_ + _).
  change ((ratr (Qval p * Qval q))%:E * f x =
    (ratr (Qval p))%:E * ((ratr (Qval q))%:E * f x)).
  by rewrite rmorphM EFinM muleA.
Qed.

Lemma enumQ_extended_expect_bind {A B} (f : B -> \bar R)
    (mu : EnumQ A) (k : A -> EnumQ B) :
  (forall x, 0 <= f x) ->
  enumQ_extended_expect f (bind_EnumQ mu k) =
    enumQ_extended_expect (fun x => enumQ_extended_expect f (k x)) mu.
Proof.
  move=> Hf. elim: mu=> [|[p x] tail IH] //=.
  by rewrite enumQ_extended_expect_app enumQ_extended_expect_scale // IH.
Qed.

Lemma enumQ_extended_expect_rat {A} (f : A -> rat) mu :
  enumQ_extended_expect (fun x => (ratr (f x))%:E) mu = (ratr (enumQ_expect f mu))%:E.
Proof.
  elim: mu=> [|[p x] tail IH] /=; first by rewrite rmorph0.
  by rewrite IH rmorphD rmorphM EFinD EFinM.
Qed.

Lemma enumQ_extended_expect_one {A} (mu : EnumQ A) :
  enumQ_extended_expect (fun _ => 1) mu = (ratr (enumQ_expect (fun _ => 1) mu))%:E.
Proof.
  rewrite (_ : (fun _ : A => (1 : \bar R)) = (fun _ => (ratr (1 : rat))%:E));
    last by apply functional_extensionality=> x; rewrite rmorph1.
  exact: enumQ_extended_expect_rat.
Qed.

Definition extended_upper (c : nat -> \bar R) := ereal_sup (range c).

Lemma extended_upper_le c b :
  (forall n, c n <= b) -> extended_upper c <= b.
Proof. move=> Hb. apply ub_ereal_sup=> x [n _ <-]. exact: Hb. Qed.

Lemma extended_upper_ge c n : c n <= extended_upper c.
Proof. apply ereal_sup_ubound. by exists n. Qed.

Lemma extended_upper_constant x : extended_upper (fun _ => x) = x.
Proof.
  apply/eqP. rewrite eq_le. apply/andP; split.
  - apply extended_upper_le=> n. exact: lexx.
  - exact: (extended_upper_ge (fun _ => x) 0%nat).
Qed.

Lemma extended_upper_mono c d :
  (forall n, c n <= d n) -> extended_upper c <= extended_upper d.
Proof.
  move=> H. apply extended_upper_le=> n.
  exact: le_trans (H n) (extended_upper_ge d n).
Qed.

Lemma extended_upper_swap (grid : nat -> nat -> \bar R) :
  extended_upper (fun i => extended_upper (grid i)) =
  extended_upper (fun j => extended_upper (fun i => grid i j)).
Proof.
  apply/eqP. rewrite eq_le. apply/andP; split;
    apply extended_upper_le=> i; apply extended_upper_le=> j.
  - eapply le_trans; [apply (extended_upper_ge (fun k => grid k j) i)|].
    exact: extended_upper_ge.
  - eapply le_trans; [apply (extended_upper_ge (grid j) i)|].
    exact: extended_upper_ge.
Qed.

Fixpoint free_omega_extended_upper {A} (mu : FreeOmega EnumQ A)
    (f : A -> \bar R) : \bar R :=
  match mu with
  | FORet x => f x
  | FOZero => 0
  | @FOSample _ _ X node k =>
      enumQ_extended_expect (fun x => free_omega_extended_upper (k x) f) node
  | FOLub c => extended_upper (fun n => free_omega_extended_upper (c n) f)
  end.

Lemma free_omega_extended_upper_nonnegative {A} (mu : FreeOmega EnumQ A)
    (f : A -> \bar R) :
  (forall x, 0 <= f x) -> 0 <= free_omega_extended_upper mu f.
Proof.
  move=> Hf. induction mu as [x| |X node k IH|c IH]; cbn [free_omega_extended_upper].
  - exact: Hf.
  - exact: lexx.
  - exact: enumQ_extended_expect_nonnegative.
  - exact: le_trans (IH 0%nat) (extended_upper_ge _ 0%nat).
Qed.

Lemma free_omega_extended_upper_mono {A} (mu : FreeOmega EnumQ A)
    (f g : A -> \bar R) :
  (forall x, f x <= g x) ->
  free_omega_extended_upper mu f <= free_omega_extended_upper mu g.
Proof.
  move=> Hfg. induction mu as [x| |X node k IH|c IH]; cbn [free_omega_extended_upper].
  - exact: Hfg.
  - exact: lexx.
  - exact: enumQ_extended_expect_mono.
  - exact: extended_upper_mono.
Qed.

Lemma free_omega_extended_upper_bind {A B} (mu : FreeOmega EnumQ A)
    (k : A -> FreeOmega EnumQ B) (f : B -> \bar R) :
  free_omega_extended_upper (free_omega_bind mu k) f =
  free_omega_extended_upper mu (fun x => free_omega_extended_upper (k x) f).
Proof.
  induction mu as [x| |X node h IH|c IH]; cbn [free_omega_bind free_omega_extended_upper].
  - reflexivity.
  - reflexivity.
  - f_equal. apply functional_extensionality. exact IH.
  - f_equal. apply functional_extensionality. exact IH.
Qed.
End ExtendedUpper.
