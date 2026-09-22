(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Prob.Backend.SubEnumQ Require Import Expectation.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteScalarMap.
From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Arith Require Import PeanoNat.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order rat reals.
From mathcomp.classical Require Import classical_sets.
From mathcomp.analysis Require Import ereal sequences.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Iteration.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.EnumQ.Support PTree.Prob.Backend.EnumQ.SemanticCoupling.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperExpectation PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperCoupling PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperContinuity PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperObservation PTree.Prob.Backend.EnumQ.FreeOmega.UpperExpectation PTree.Prob.Backend.EnumQ.FreeOmega.UpperCoupling PTree.Prob.Backend.EnumQ.FreeOmega.UpperContinuity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory Order.Theory EnumQCouplingClassical.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

(** The existing rational-limit lemmas are backend-independent despite
    their historical SubEnumQ filename.  Reuse them rather than assuming
    that a raw EnumQ or its intermediate terms have mass at most one. *)
Section ExtendedObservation.
Variable R : realType.

Lemma enumQ_extended_expect_real {A} (f : A -> R) mu :
  enumQ_extended_expect (fun x => (f x)%:E) mu = (enumQ_real_expect f mu)%:E.
Proof.
  rewrite /enumQ_extended_expect /enumQ_real_expect.
  elim: (enumQ_raw mu)=> [|[p x] tail IH]; first reflexivity.
  by rewrite /finite_map_weights /= IH EFinD EFinM.
Qed.

Lemma extended_upper_real (c : nat -> R) b :
  (forall n, (c n <= b)%R) ->
  extended_upper (fun n => (c n)%:E) = (countable_upper c)%:E.
Proof.
  move=> Hb. rewrite /extended_upper /countable_upper.
  have E : range (fun n => (c n)%:E) = EFin @` range c.
  { rewrite -image_comp. reflexivity. }
  rewrite E. apply ereal_sup_EFin.
  - exists b. intros x [n _ <-]. exact: Hb.
  - exists (c 0%nat). by exists 0%nat.
Qed.

Lemma enumQ_monotone_real_expect_bound_eqtype {A : eqType}
    (chain : nat -> EnumQ A) out (f : A -> R) :
  enumQ_chain_increasing chain -> enumQ_converges chain out ->
  (forall x, (0 <= f x)%R) ->
  forall n, (enumQ_real_expect f (chain n) <= enumQ_real_expect f out)%R.
Proof.
  move=> Hinc Hlim Hf n. apply enumQ_real_expect_atom_le; [exact Hf|].
  intro x. rewrite ler_rat.
  apply (rat_monotone_limit_bound
    (values := fun i => acc_mass x (chain i))).
  - intro i. rewrite -!enumQ_indicator_atom.
    exact (Hinc (fun y => y == x) i (S i) (Nat.le_succ_diag_r i)).
  - intros eps Heps. destruct (Hlim (fun y => y == x) eps Heps) as [N HN].
    exists N. intros i Hi. rewrite -!enumQ_indicator_atom. exact (HN i Hi).
Qed.

Lemma enumQ_monotone_real_expect_bound {A : Type}
    (chain : nat -> EnumQ A) out (f : A -> R) :
  enumQ_chain_increasing chain -> enumQ_converges chain out ->
  (forall x, (0 <= f x)%R) ->
  forall n, (enumQ_real_expect f (chain n) <= enumQ_real_expect f out)%R.
Proof.
  exact (@enumQ_monotone_real_expect_bound_eqtype
    (@Equality.Pack (EnumQCouplingClassical.carrier A)
      (Equality.on (EnumQCouplingClassical.carrier A))) chain out f).
Qed.

Theorem free_omega_observes_extended_real {A O} (obs : A -> O)
    (mu : FreeOmega EnumQ A) (out : EnumQ O) :
  @free_omega_observes EnumQ EnumQ_SemanticMeasure EnumQ_SemanticOmega
    A O obs mu out ->
  forall f : O -> R, (forall y, (0 <= f y)%R) ->
    free_omega_extended_upper mu (fun x => (f (obs x))%:E) =
      (enumQ_real_expect f out)%:E.
Proof.
  intro Hobs. induction Hobs as [x| |X node k front Hobs IH|chain outs out Hobs IH Hlim Hinc];
    intros f Hf.
  - change ((f (obs x))%:E = (ratr (1 : rat) * f (obs x) + 0)%R%:E).
    by rewrite rmorph1 mul1r addr0.
  - reflexivity.
  - change (enumQ_extended_expect
      (fun x => free_omega_extended_upper (k x) (fun y => (f (obs y))%:E)) node =
      (enumQ_real_expect f (bind_EnumQ node front))%:E).
    rewrite enumQ_real_expect_bind -enumQ_extended_expect_real.
    f_equal. apply functional_extensionality=> x. exact (IH x f Hf).
  - cbn [free_omega_extended_upper].
    have Hrows : (fun n => free_omega_extended_upper (chain n) (fun x => (f (obs x))%:E)) =
      (fun n => (enumQ_real_expect f (outs n))%:E).
    { apply functional_extensionality=> n. exact (IH n f Hf). }
    have Hmono : enumQ_chain_increasing outs.
    { intros P n m Hnm.
      have HP : forall y, (0 <= (if P y then (1 : R) else 0))%R.
      { intro y. destruct (P y); [exact: ler01|exact: lexx]. }
      have Hstep : forall i,
        (@enumQ_real_expect R O (fun y => if P y then 1 else 0) (outs i) <=
         @enumQ_real_expect R O (fun y => if P y then 1 else 0) (outs (S i)))%R.
      { intro i. rewrite -lee_fin -(IH i _ HP) -(IH (S i) _ HP).
        eapply free_omega_approx_extended_upper; [exact (Hinc i)| |].
        - intro x. rewrite lee_fin. exact (HP (obs x)).
        - intros x y ->. exact: lexx. }
      have Hreal := scalar_increasing_le Hstep Hnm.
      rewrite !enumQ_real_expect_indicator ler_rat in Hreal. exact Hreal. }
    rewrite Hrows (extended_upper_real
      (enumQ_monotone_real_expect_bound Hmono Hlim Hf)).
    by rewrite (enumQ_monotone_converges_upper Hmono Hlim Hf).
Qed.

(** Real stages of a nonnegative extended test.  A finite value remains
    constant; +oo is approached by naturals.  No uniform finite bound is
    needed on the stages or on the observable carrier. *)
Definition extended_real_stage (n : nat) (x : \bar R) : R :=
  match x with EFin r => r | EPInf => n%:R | ENInf => 0%R end.

Lemma extended_real_stage_nonnegative n x :
  0 <= x -> (0 <= extended_real_stage n x)%R.
Proof. destruct x; cbn; intro H; [exact H|exact: ler0n|exact: lexx]. Qed.

Lemma extended_real_stage_increasing x :
  nondecreasing_seq (fun n => (extended_real_stage n x)%:E).
Proof.
  destruct x; intros n m Hnm; cbn; rewrite ?lee_fin; try exact: lexx.
  by rewrite ler_nat.
Qed.

Lemma extended_real_stage_sup x : 0 <= x ->
  extended_upper (fun n => (extended_real_stage n x)%:E) = x.
Proof.
  destruct x; cbn; intro H.
  - exact: extended_upper_constant.
  - exact: extended_upper_naturals.
  - discriminate H.
Qed.

Theorem free_omega_observes_extended_upper {A O} (obs : A -> O)
    (mu : FreeOmega EnumQ A) (out : EnumQ O) (f : O -> \bar R) :
  @free_omega_observes EnumQ EnumQ_SemanticMeasure EnumQ_SemanticOmega
    A O obs mu out ->
  (forall y, 0 <= f y) ->
  free_omega_extended_upper mu (fun x => f (obs x)) = enumQ_extended_expect f out.
Proof.
  intros Hobs Hf.
  pose tests n y := (extended_real_stage n (f y))%:E.
  have Htests : forall n y, 0 <= tests n y.
  { intros n y. rewrite /tests lee_fin. exact: extended_real_stage_nonnegative. }
  have Hinc : forall y, nondecreasing_seq (fun n => tests n y).
  { intro y. exact: extended_real_stage_increasing. }
  have Ef : (fun y => extended_upper (fun n => tests n y)) = f.
  { apply functional_extensionality=> y. exact: extended_real_stage_sup. }
  have Eobs : (fun x => extended_upper (fun n => tests n (obs x))) =
      (fun x => f (obs x)).
  { apply functional_extensionality=> x. exact: extended_real_stage_sup. }
  have Hmu := @free_omega_extended_upper_continuous R A mu
    (fun n x => tests n (obs x)) (fun n x => Htests n (obs x))
    (fun x => Hinc (obs x)).
  have Hout := @enumQ_extended_expect_countable R O out tests Htests Hinc.
  rewrite Eobs in Hmu. rewrite Ef in Hout. rewrite Hmu Hout.
  f_equal. apply functional_extensionality=> n.
  rewrite /tests enumQ_extended_expect_real.
  exact (@free_omega_observes_extended_real A O obs mu out Hobs
    (fun y => extended_real_stage n (f y))
    (fun y => extended_real_stage_nonnegative n (Hf y))).
Qed.
End ExtendedObservation.
