(** Relational-limit contracts: no normalization, finite-support restriction,
    or coherent-joint premise in the countable transport route. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssralg ssrnum order reals.
From PTree.Prob.Domain Require Import Expectation Countable Coupling RelationalLimit.
From PTree.Prob.Backend.Common Require Import CountableRelationalLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Core.PTreeDefinition.ptree.

Section CountableTests.
Variable R : realType.

Lemma nat_countable (L : OmegaVal R nat) : oval_countably_supported L.
Proof.
  exists (@Some nat); intros f g Hf Hg Hfg.
  apply oval_eval_ext=> n; apply Hfg; exists n; reflexivity.
Qed.

(** Truly arbitrary nat distributions, not only finite approximants. Both
    limiting marginals may have infinite support and deficient total mass. *)
Example arbitrary_nat_relational_limit (T : nat -> nat -> Prop)
    (c d : nat -> OmegaVal R nat)
    (Hc : oval_increasing c) (Hd : oval_increasing d) :
  (forall n, oval_coupled T (c n) (d n)) ->
  exists J, oval_joint T (oval_lub Hc) (oval_lub Hd) J.
Proof. apply oval_coupled_lub; intro n; apply nat_countable. Qed.

Example successor_limit (c : nat -> OmegaVal R nat) (Hc : oval_increasing c) :
  oval_coupled (fun x y => y = S x) (oval_lub Hc)
    (oval_lub (oval_bind_chain_l Hc (fun x => oval_ret R (S x)))).
Proof.
  apply oval_coupled_lub; try (intro n; apply nat_countable).
  intro n; exists (oval_bind (c n) (fun x => oval_ret R (x,S x))).
  split; first by intros.
  split; first by intros.
  intros f g Hf Hg Hfg.
  change (oval_eval (c n) (fun x => f (x,S x)) = oval_eval (c n) (fun x => g (x,S x))).
  apply oval_eval_ext=> x.
  apply (Hfg (x,S x)); reflexivity.
Qed.

Example equality_limit (c d : nat -> OmegaVal R nat)
    (Hc : oval_increasing c) (Hd : oval_increasing d) :
  (forall n, oval_coupled eq (c n) (d n)) ->
  oval_eq (oval_lub Hc) (oval_lub Hd).
Proof.
  intro H; apply (proj1 (oval_eq_coupled_iff _ _)).
  exact (arbitrary_nat_relational_limit Hc Hd H).
Qed.

Example empty_relation_zero_limit :
  oval_coupled (fun (_ : Empty_set) (_ : bool) => False)
    (oval_lub (fun n => @oval_le_refl R Empty_set (oval_bottom R)))
    (oval_lub (fun n => @oval_le_refl R bool (oval_bottom R))).
Proof.
  apply oval_coupled_lub.
  - intro n; exists (fun _ => None); intros f g Hf Hg Hfg; reflexivity.
  - intro n; exists (fun _ => None); intros f g Hf Hg Hfg; reflexivity.
  - intro n; exists (@oval_bottom R (Empty_set * bool)).
    split; first by intros. split; first by intros.
    intros f g Hf Hg Hfg; reflexivity.
Qed.
End CountableTests.

(** An explicit finite obstruction to extending a previously selected joint.
    At level zero half the mass is at (true,true). The next marginals are
    fair, but the relation forbids (false,false), forcing a crossed joint.
    Consequently no next joint can dominate the selected first joint. *)
From PTree.Prob.Backend.SubEnumR Require Import Representation Domain.
From PTree.Prob.Backend.Common Require Import FiniteSubdist.

Section NoncoherentJoints.
Variable R : realType.
Lemma half_nonnegative : (0 : R) <= 2^-1.
Proof. by rewrite invr_ge0 ler0n. Qed.
Lemma half_bound : (2^-1 : R) <= 1.
Proof. by rewrite invf_le1 // ler1n. Qed.
Lemma half_complement : (1 - 2^-1 : R) = 2^-1.
Proof. by rewrite {1}(splitr (1 : R)) mul1r addrK. Qed.

Definition fair : OmegaVal R bool :=
  subenumR_domain (subenumR_coin half_nonnegative half_bound).
Definition half_point {A} (x : A) : OmegaVal R A :=
  subenumR_domain (finite_subdist_scale half_nonnegative half_bound (subenumR_ret R x)).

Lemma fair_eval f : oval_eval fair f = 2^-1 * f true + 2^-1 * f false.
Proof.
  change (2^-1 * f true + ((1 - 2^-1) * f false + 0) =
    2^-1 * f true + 2^-1 * f false).
  by rewrite addr0 half_complement.
Qed.
Lemma half_eval {A} (x : A) f : oval_eval (half_point x) f = 2^-1 * f x.
Proof.
  change ((2^-1 * 1) * f x + 0 = 2^-1 * f x).
  by rewrite addr0 mulr1.
Qed.

Definition allowed (x y : bool) : Prop := x = true \/ y = true.
Definition bit (b : bool) : R := if b then 1 else 0.
Definition both (p : bool * bool) : R := if (fst p && snd p) then 1 else 0.
Lemma bit_test : oval_test bit.
Proof. intros []; split; try exact: lexx; exact: ler01. Qed.
Lemma both_test : oval_test both.
Proof. intros [[] []]; split; try exact: lexx; exact: ler01. Qed.

Lemma half_le_fair : oval_le (half_point true) fair.
Proof.
  intros f Hf; rewrite half_eval fair_eval lerDl.
  exact (mulr_ge0 half_nonnegative (proj1 (Hf false))).
Qed.

Lemma initial_joint :
  oval_joint allowed (half_point true) (half_point true) (half_point (true,true)).
Proof.
  split; first by intros; rewrite !half_eval.
  split; first by intros; rewrite !half_eval.
  intros f g Hf Hg Hfg; rewrite !half_eval.
  rewrite (Hfg (true,true)); [reflexivity|left; reflexivity].
Qed.

Lemma final_joint :
  oval_joint allowed fair fair (oval_bind fair (fun b => oval_ret R (b,negb b))).
Proof.
  split; first by intros.
  split.
  - intros f Hf; change (oval_eval fair (fun b => f (negb b)) = oval_eval fair f).
    by rewrite !fair_eval /= addrC.
  - intros f g Hf Hg Hfg.
    change (oval_eval fair (fun b => f (b,negb b)) = oval_eval fair (fun b => g (b,negb b))).
    apply oval_eval_ext=> b.
    apply (Hfg (b,negb b)); destruct b; [left|right]; reflexivity.
Qed.

Lemma final_joint_no_diagonal (J : OmegaVal R (bool * bool)) :
  oval_joint allowed fair fair J -> oval_eval J both = 0.
Proof.
  intros [Hl [Hr Hae]].
  pose left_false (p : bool * bool) := bit (negb (fst p)).
  have Hlf : oval_test left_false by intros [x y]; exact (bit_test (negb x)).
  have Hsum : forall p, both p + left_false p <= 1.
  { intros [[] []]; rewrite /both /left_false /bit /= ?addr0 ?add0r;
      try exact: lexx; exact: ler01. }
  have He := Hae (fun p => bit (snd p)) (fun p => both p + left_false p)
    (fun p => bit_test (snd p)) (oval_test_add both_test Hlf Hsum).
  have Hpoint : forall p, allowed (fst p) (snd p) ->
      bit (snd p) = both p + left_false p.
  { intros [[] []]; rewrite /allowed /both /left_false /bit /= ?addr0 ?add0r;
      intros H; try reflexivity; destruct H; discriminate. }
  specialize (He Hpoint).
  rewrite (oval_add (oval_laws J) both_test Hlf Hsum) in He.
  rewrite (Hr bit bit_test) (Hl (fun b => bit (negb b)) (fun b => bit_test (negb b))) in He.
  rewrite !fair_eval /bit /= !mulr1 !mulr0 addr0 add0r in He.
  apply (addIr (2^-1 : R)). by rewrite add0r -He.
Qed.

Theorem initial_joint_has_no_increasing_extension :
  ~ exists J, oval_joint allowed fair fair J /\ oval_le (half_point (true,true)) J.
Proof.
  intros [J [HJ Hle]]. have Hbad := Hle both both_test.
  rewrite half_eval (final_joint_no_diagonal HJ) /both /= mulr1 in Hbad.
  have Hpos : (0 : R) < 2^-1 by rewrite invr_gt0 ltr0n.
  by move: Hpos; rewrite ltNge Hbad.
Qed.

(** This is not just a badly chosen first witness: every first joint has
    the same positive diagonal mass, so NO coherent joint chain exists. *)
Lemma any_initial_joint_diagonal (J : OmegaVal R (bool * bool)) :
  oval_joint allowed (half_point true) (half_point true) J ->
  oval_eval J both = 2^-1.
Proof.
  intros [Hl [Hr Hae]].
  pose bad (p : bool * bool) := if (fst p && ~~ snd p) then (1 : R) else 0.
  have Hb : oval_test bad.
  { intros [[] []]; split; try exact: lexx; exact: ler01. }
  have Hbadle : oval_eval J bad <= oval_eval J (fun p => bit (negb (snd p))).
  { apply (oval_mono (oval_laws J) Hb (fun p => bit_test (negb (snd p)))).
    intros [[] []]; try exact: lexx; exact: ler01. }
  rewrite (Hr (fun b => bit (negb b)) (fun b => bit_test (negb b)))
    half_eval /bit /= mulr0 in Hbadle.
  have Hbadzero : oval_eval J bad = 0.
  { apply/eqP; rewrite eq_le; apply/andP; split; first exact Hbadle.
    exact (proj1 (oval_eval_bounds J Hb)). }
  have Hsum : forall p, both p + bad p <= 1.
  { intros [[] []]; rewrite /both /bad /= ?addr0 ?add0r;
      try exact: lexx; exact: ler01. }
  have He : oval_eval J (fun p => bit (fst p)) = oval_eval J (fun p => both p + bad p).
  { apply oval_eval_ext; intros [[] []]; by rewrite /bit /both /bad /= ?addr0 ?add0r. }
  rewrite (Hl bit bit_test) half_eval /bit /= mulr1
    (oval_add (oval_laws J) both_test Hb Hsum) Hbadzero addr0 in He.
  symmetry; exact He.
Qed.

Definition growing_marginals n := match n with
  | O => half_point true | S _ => fair end.
Lemma growing_marginals_increasing : oval_increasing growing_marginals.
Proof. intros [|n]; [apply half_le_fair|apply oval_le_refl]. Qed.
Lemma growing_marginals_coupled n :
  oval_coupled allowed (growing_marginals n) (growing_marginals n).
Proof.
  destruct n as [|n].
  - eexists; exact initial_joint.
  - eexists; exact final_joint.
Qed.

Theorem no_increasing_joint_selection :
  ~ exists j : nat -> OmegaVal R (bool * bool),
    oval_increasing j /\
    forall n, oval_joint allowed (growing_marginals n) (growing_marginals n) (j n).
Proof.
  intros [j [Hi Hj]]. have Hbad := Hi O both both_test.
  rewrite (any_initial_joint_diagonal (Hj O))
    (final_joint_no_diagonal (Hj (S O))) in Hbad.
  have Hpos : (0 : R) < 2^-1 by rewrite invr_gt0 ltr0n.
  by move: Hpos; rewrite ltNge Hbad.
Qed.

(** Nevertheless the true relational-limit theorem succeeds. *)
Example noncoherent_chain_has_limit_joint :
  oval_coupled allowed (oval_lub growing_marginals_increasing)
    (oval_lub growing_marginals_increasing).
Proof.
  have Hcount : forall L : OmegaVal R bool, oval_countably_supported L.
  { intro L; exists (fun i => Some (Nat.even i)); intros f g Hf Hg Hfg.
    apply oval_eval_ext; intros []; apply Hfg;
      [exists O|exists (S O)]; reflexivity. }
  apply oval_coupled_lub.
  - intro n; apply Hcount.
  - intro n; apply Hcount.
  - exact growing_marginals_coupled.
Qed.
End NoncoherentJoints.

(** A normally universe-checked native MathComp client. This is NOT the
    unrestricted pointwise-lifting limit theorem: joint monotonicity and
    exact marginal certificates are explicit premises. No PTree assembly. *)
From PTree.Prob.Interface Require Import Measure Omega RelationalLimit.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure OmegaLaws BindLaws.
Section NativeMathComp.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation MI := (MathCompNodeSemanticMeasure R).
Local Notation MO := (MathCompNodeSemanticOmega R).

Example mathcomp_coherent_joint_limit {A B} (T : A -> B -> Prop)
    (c : nat -> M A) (d : nat -> M B) (j : nat -> M (A * B)) mu nu :
  @sem_increasing M MI MO _ j ->
  sem_lub c mu -> sem_lub d nu ->
  (forall n, sem_eq (sem_bind (j n) (fun p => sem_ret (fst p))) (c n)) ->
  (forall n, sem_eq (sem_bind (j n) (fun p => sem_ret (snd p))) (d n)) ->
  (forall n, sem_ae (j n) (fun p => T (fst p) (snd p))) ->
  sem_lift T mu nu.
Proof.
  exact (sem_lift_lub_of_joint_chain (R := T) (left := c) (right := d)
    (joints := j) (out1 := mu) (out2 := nu)).
Qed.
End NativeMathComp.
