Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.

Require Import Program.Equality FunctionalExtensionality Arith.PeanoNat Lia Ring Field.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssralg ssrnum order rat.
From PTree.Core Require Import PTreeDefinition PTreeProbability.
From PTree.Prob Require Import RatSubTypes DiscreteMC TwoLevelMeasure
  TwoLevelMeasureEnum TwoLevelMeasureSubEnum FreeOmegaMeasure
  MeasureIterationEnum RatGeometric.
From PTree.Eq Require Import Shallow PStruct PStrong PEutt FreeOmega
  UnifiedFrontier PrimitiveStableHitting PTreeKernel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** An infinite-state random walk with a closed-form joint output law.
    With probability 2/3, decrement the height and increment the streak;
    otherwise increment the height and reset the streak to zero.  Starting
    from [(1,0)], the loop terminates almost surely, with
      Pr[(x,y) = (0,n)] = 2 / 3^n, n >= 1,
    and zero probability elsewhere.

    [run_split] and [passage_unfold] expose one-level passages using actual
    tree equations.  A bounded harmonic candidate and a rational error bound
    then certify the closed form against primitive execution approximants.
    [random_walk_closed_form] packages native AST, the finite observation
    bridge, the pointwise law, and normalization.  This output-distribution
    endpoint does not assume a converse from equal PMFs to [peutt]. *)
Section PassageControlFlow.
Context {E M : Type -> Type}.
Variable coin : M bool.

Definition rw_state := (nat * nat)%type.

Definition rw_next (x y : nat) (down : bool) : rw_state :=
  if down then (x, S y) else (S (S x), 0).

Definition rw_body (s : rw_state) : ptree E M (rw_state + rw_state) :=
  let '(x,y) := s in
  match x with
  | O => Ret (inr (0,y))
  | S x' => Prob coin (fun down => Ret (inl (rw_next x' y down)))
  end.

Definition passage_body (s : rw_state) : ptree E M (rw_state + nat) :=
  let '(x,y) := s in
  match x with
  | O => Ret (inr y)
  | S x' => Prob coin (fun down => Ret (inl (rw_next x' y down)))
  end.

Definition run_until_zero (x y : nat) : ptree E M nat :=
  PTree.iter passage_body (x,y).

Definition passage (y : nat) := run_until_zero 1 y.
Definition D0 := passage 0.
Definition passage_tail := PTree.bind D0 passage.
Definition random_walk_prog : ptree E M rw_state :=
  PTree.iter rw_body (1,0).

Lemma run_zero_observe y : observe (run_until_zero 0 y) = RetF y.
Proof. reflexivity. Qed.

Definition run_branch x y down : ptree E M nat :=
  PTree.bind (Ret (inl (rw_next x y down)))
    (fun next : rw_state + nat =>
      match next with
      | inl s => Tau (PTree.iter passage_body s)
      | inr r => Ret r
      end).

Lemma run_succ_observe x y :
  observe (run_until_zero (S x) y) =
  ProbF coin (run_branch x y).
Proof. reflexivity. Qed.

Lemma run_branch_observe x y down :
  observe (run_branch x y down) =
  TauF (let '(x',y') := rw_next x y down in run_until_zero x' y').
Proof. destruct down; reflexivity. Qed.

(** The generic stopping law handles the control flow.  The only local
    invariant is height translation by [b], preserving the streak.  Reaching
    relative height zero returns the state at the intermediate barrier. *)
Theorem run_split a b y :
  pstruct eq (run_until_zero (a+b) y)
    (PTree.bind (run_until_zero a y) (run_until_zero b)).
Proof.
  unfold run_until_zero.
  eapply pstruct_iter_split_at with
    (SI := fun i j => i = (Nat.add (fst j) b, snd j))
    (resume := fun z => (b,z)).
  - intros i [h z] Hstate. cbn in Hstate. subst i.
    destruct h as [|h].
    + left. exists z. split; reflexivity.
    + right. apply pstruct_fold. cbn. apply PStProb. intros down.
      apply pstruct_fold. cbn. apply PStRet. constructor.
      destruct down; reflexivity.
  - reflexivity.
Qed.

Lemma height_two_split :
  pstruct eq (run_until_zero 2 0) passage_tail.
Proof. exact (run_split 1 1 0). Qed.

Lemma passage_unfold_guarded y :
  pstruct eq (passage y)
    (Prob coin (fun down =>
      Tau (if down then Ret (S y) else passage_tail))).
Proof.
  apply pstruct_fold. unfold passage. rewrite run_succ_observe. cbn.
  apply PStProb. intro down. apply pstruct_fold.
  rewrite run_branch_observe. destruct down; cbn [rw_next observe].
  - apply PStTau. apply observe_eq_pstruct. apply run_zero_observe.
  - apply PStTau. exact height_two_split.
Qed.

Lemma random_walk_result_relation x y :
  pstruct (fun s n => s = (0,n))
    (PTree.iter rw_body (x,y)) (run_until_zero x y).
Proof.
  unfold run_until_zero.
  eapply pstruct_iter_rel with (SI := eq).
  - intros s [h z] Hs. subst s. destruct h as [|h]; apply pstruct_fold; cbn.
    + constructor. constructor. reflexivity.
    + apply PStProb. intro down. apply pstruct_fold; cbn.
      constructor. constructor. reflexivity.
  - reflexivity.
Qed.

Theorem random_walk_as_passage :
  pstruct eq random_walk_prog (PTree.fmap (fun n => (0,n)) D0).
Proof.
  unfold random_walk_prog, D0, passage, PTree.fmap.
  eapply pstruct_trans.
  - apply pstruct_sym. apply pstruct_bind_ret_r.
  - eapply pstruct_bind with (RA := fun s n => s = (0,n)).
    + intros s n ->. apply pstruct_refl.
    + apply random_walk_result_relation.
Qed.

End PassageControlFlow.

Import Enum RatSubTypes GRing.Theory Order.Theory.
Import RatSubTypes.NonnegQNotations.
Local Open Scope ring_scope.
Local Open Scope order_scope.

#[program] Definition rw_down_weight : nnQ := [nn 2/3].
#[program] Definition rw_up_weight : nnQ := [nn 1/3].
Definition rw_coin_raw : Enum bool :=
  [:: (rw_down_weight, true); (rw_up_weight, false)].

Lemma rw_coin_subprob : enum_subprob rw_coin_raw.
Proof.
  rewrite /enum_subprob /enum_mass /rw_coin_raw /= !mulr1 addr0.
  native_compute. reflexivity.
Qed.

Definition rw_coin : SubEnum bool :=
  @enum_as_subprob bool rw_coin_raw rw_coin_subprob.

Unset Automatic Proposition Inductives.
Variant rwE : Type -> Type := .
Local Notation rwFI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation rwFO := (@FreeOmegaObservableSemanticOmega
  SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
Local Notation rwpeutt :=
  (@peutt rwE SubEnum (FreeOmega SubEnum)
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega).

Definition random_walk : ptree rwE SubEnum rw_state := random_walk_prog rw_coin.
Definition rw_passage : nat -> ptree rwE SubEnum nat := passage rw_coin.
Definition rw_D0 := rw_passage 0.
Definition rw_continuation := PTree.bind rw_D0 rw_passage.

Lemma random_walk_probabilistic : probabilistic_ptree random_walk.
Proof. apply probabilistic_ptree_intrinsic. Qed.

Theorem random_walk_passage_normal_form :
  rwpeutt eq random_walk (PTree.fmap (fun n => (0%nat,n)) rw_D0).
Proof.
  apply peutt_of_pstruct.
  apply random_walk_as_passage.
Qed.

(** Structural normalization exposes one administrative Tau per branch.
    Tau transparency and probabilistic contextual rewriting are already
    derived from stable hitting; no intermediate finite equivalence or
    native coupling-realization capability is needed.  The continuations
    may themselves perform unbounded retries. *)
Theorem passage_unfold y :
  rwpeutt eq (rw_passage y)
    (Prob rw_coin (fun down =>
      if down then Ret (S y) else rw_continuation)).
Proof.
  eapply peutt_trans.
  - apply peutt_of_pstruct. apply passage_unfold_guarded.
  - eapply peutt_prob with (XR := eq).
    + apply sem_lift_refl. intro down. reflexivity.
    + intros down down' ->. apply peutt_tau_l.
Qed.

(** Quantitative semantics (separate from finite administrative rewrites).
    The analytic part uses rational finite approximants.  A countable output
    is specified by the limits of its individual masses, without packaging
    infinitely many atoms into the finite [SubEnum] carrier.

    The renewal route m = p + q*m*m would first need an existing scalar
    mass for each completed passage, and an unconditional observation/bind
    theorem computing the mass of C from those scalars.  [sem_total] is a
    predicate, not such a mass function.  [free_omega_denotes_bind] is an
    additional capability, not an available SubEnum instance, and requires
    represented observations up front.  The atom calculation likewise needs
    integration against D0's countably supported law, which cannot itself be
    represented in finite SubEnum.  Thus assuming those limits here would
    beg the existence question.  We retain the constructive rational-limit
    argument; no scalar cancellation or PMF-to-peutt converse is assumed. *)
Import Num.Theory.
(** Unlike [ring_to_rat], do not simplify concrete rational multiplication:
    doing so unfolds its representation before the ring tactic runs. *)
Local Ltac rw_rat :=
  rewrite ?mulrS ?mulr0n;
  rewrite -?[0%R]/0%Q -?[1%R]/1%Q
          -?[(_ - _)%R]/(_ - _)%Q -?[(_ / _)%R]/(_ / _)%Q
          -?[(_ + _)%R]/(_ + _)%Q -?[(_ * _)%R]/(_ * _)%Q
          -?[(- _)%R]/(- _)%Q -?[(_ ^-1)%R]/(_ ^-1)%Q;
  match goal with |- @eq _ ?a ?b => change (@eq rat a b) end.
Local Notation p := (2 / 3 : rat).
Local Notation q := (1 / 3 : rat).

Lemma rw_p_nonnegative : 0 <= p.
Proof. native_compute. reflexivity. Qed.
Lemma rw_q_nonnegative : 0 <= q.
Proof. native_compute. reflexivity. Qed.
Lemma rw_p_le_one : p <= 1.
Proof. native_compute. reflexivity. Qed.
Lemma rw_q_le_one : q <= 1.
Proof. native_compute. reflexivity. Qed.

Definition geometric_pmf (n : nat) : rat :=
  match n with O => 0 | S k => p * q ^+ k end.

Definition joint_pmf (s : rw_state) : rat :=
  match s with (O, n) => geometric_pmf n | _ => 0 end.

Lemma geometric_recurrence n k :
  geometric_pmf (n-k)%nat =
  p * (if Nat.eqb n (S k) then 1 else 0) +
  q * geometric_pmf (n-S k)%nat.
Proof.
  revert n. induction k as [|k IH]; intros [|n]; cbn [Nat.sub Nat.eqb].
  - rewrite /geometric_pmf mulr0 add0r mulr0. reflexivity.
  - destruct n as [|n]; cbn [Nat.sub Nat.eqb geometric_pmf].
    + rewrite !mulr1 mulr0 addr0. reflexivity.
    + rewrite subn0 /geometric_pmf exprS mulr0 add0r mulrCA. reflexivity.
  - rewrite /geometric_pmf !mulr0 add0r. reflexivity.
  - exact (IH n).
Qed.

Fixpoint reset_mass (x n : nat) : rat :=
  match x with
  | O => 0
  | S k => reset_mass k n + q * p ^+ k * geometric_pmf (n-S k)%nat
  end.

(** The first term accounts for never resetting before absorption.  The
    second term groups paths by how many levels precede the final reset. *)
Definition passage_pmf (x y n : nat) : rat :=
  p ^+ x * (if Nat.eqb n (y+x)%nat then 1 else 0) + reset_mass x n.

Lemma passage_pmf_zero y n :
  passage_pmf 0 y n = (if Nat.eqb n y then 1 else 0).
Proof. by rewrite /passage_pmf addn0 expr0 mul1r addr0. Qed.

Lemma passage_pmf_reset x n :
  passage_pmf (S x) 0 n = reset_mass x n + p ^+ x * geometric_pmf (n-x)%nat.
Proof.
  rewrite /passage_pmf add0n.
  change (p ^+ S x * (if Nat.eqb n (S x) then 1 else 0) +
    (reset_mass x n + q * p ^+ x * geometric_pmf (n-S x)%nat) =
    reset_mass x n + p ^+ x * geometric_pmf (n-x)%nat).
  rewrite (geometric_recurrence n x) exprS.
  rw_rat. ring.
Qed.

Lemma passage_pmf_harmonic x y n :
  passage_pmf (S x) y n =
  p * passage_pmf x (S y) n + q * passage_pmf (S (S x)) 0 n.
Proof.
  rewrite passage_pmf_reset /passage_pmf addnS addSn.
  cbn [reset_mass].
  rewrite !exprS.
  rw_rat. field; vm_compute; intuition discriminate.
Qed.

Lemma passage_pmf_initial n : passage_pmf 1 0 n = geometric_pmf n.
Proof.
  rewrite passage_pmf_reset /= mul1r add0r subn0.
  reflexivity.
Qed.

Lemma geometric_pmf_bound n : 0 <= geometric_pmf n <= 1.
Proof.
  destruct n as [|n]; first by rewrite /geometric_pmf lexx ler01.
  apply/andP. split.
  - exact (mulr_ge0 rw_p_nonnegative (exprn_ge0 n rw_q_nonnegative)).
  - apply: le_trans (_ : p * 1 <= 1).
    + apply (ler_wpM2l rw_p_nonnegative).
      apply exprn_ile1; [exact rw_q_nonnegative|exact rw_q_le_one].
    + by rewrite mulr1; exact rw_p_le_one.
Qed.

Lemma reset_mass_bound x n :
  0 <= reset_mass x n /\ reset_mass x n <= 1 - p ^+ x.
Proof.
  induction x as [|x [H0 H1]]; first by rewrite /= expr0 subrr.
  cbn [reset_mass].
  have Hp := exprn_ge0 x rw_p_nonnegative.
  have Hg := geometric_pmf_bound (n-S x)%nat.
  have [Hg0 Hg1] := andP Hg.
  split.
  - exact (addr_ge0 H0 (mulr_ge0 (mulr_ge0 rw_q_nonnegative Hp) Hg0)).
  - apply: le_trans (lerD H1 (ler_wpM2l _ Hg1)) _.
    + exact (mulr_ge0 rw_q_nonnegative Hp).
    + have Heq : (1 - p ^+ x) + q * p ^+ x * 1 = 1 - p ^+ S x.
      { rewrite exprS. rw_rat. field; vm_compute; intuition discriminate. }
      by rewrite Heq.
Qed.

Lemma passage_pmf_bound x y n : 0 <= passage_pmf x y n <= 1.
Proof.
  have [HB0 HB1] := reset_mass_bound x n.
  have Hp := exprn_ge0 x rw_p_nonnegative.
  rewrite /passage_pmf. destruct (Nat.eqb n (y+x)%nat); rewrite ?mulr1 ?mulr0.
  - apply/andP. split; first exact: addr_ge0 Hp HB0.
    apply: le_trans (lerD (lexx _) HB1) _.
    by rewrite addrC subrK.
  - rewrite add0r. apply/andP. split; first exact HB0.
    apply: le_trans HB1 _. by rewrite lerBlDr lerDl.
Qed.

(** [rounds] counts complete sample/Tau pairs, not an artificial bound on
    the walk's state space.  The absorbing state is observed immediately. *)
Fixpoint walk_observation {A} (obs : nat -> A) (rounds x y : nat) : SubEnum A :=
  match x with
  | O => subenum_ret (obs y)
  | S h =>
      subenum_bind rw_coin (fun down =>
        match rounds with
        | O => subenum_zero
        | S fuel => if down then walk_observation obs fuel h (S y)
                    else walk_observation obs fuel (S (S h)) 0
        end)
  end.

(** The identity observation is a specialization, not a second execution
    recurrence.  [walk_hitting_observes] below certifies this executable fold
    against the maintained primitive kernel; [walk_eval] is its scalar fold. *)
Definition walk_approx (rounds x y : nat) : SubEnum nat :=
  walk_observation (fun n => n) rounds x y.

Fixpoint walk_eval (rounds : nat) (f : nat -> rat) (x y : nat) : rat :=
  match x with
  | O => f y
  | S h =>
      match rounds with
      | O => 0
      | S fuel => p * walk_eval fuel f h (S y) +
                  q * walk_eval fuel f (S (S h)) 0
      end
  end.

Lemma rw_coin_expect (f : bool -> rat) :
  enum_expect f (subenum_raw rw_coin) = p * f true + q * f false.
Proof.
  change (p * f true + (q * f false + 0) = p * f true + q * f false).
  by rewrite addr0.
Qed.

Lemma walk_observation_expect {A} (obs : nat -> A) f rounds x y :
  enum_expect f (subenum_raw (walk_observation obs rounds x y)) =
    walk_eval rounds (fun n => f (obs n)) x y.
Proof.
  revert x y. induction rounds as [|rounds IH]; intros [|x] y.
  - exact (enum_expect_ret f (obs y)).
  - change (enum_expect f (bind_Enum (subenum_raw rw_coin)
      (fun _ => [::])) = 0).
    rewrite enum_expect_bind rw_coin_expect /= !mulr0 addr0. reflexivity.
  - exact (enum_expect_ret f (obs y)).
  - change (enum_expect f (bind_Enum (subenum_raw rw_coin)
      (fun b => subenum_raw (if b then walk_observation obs rounds x (S y)
                            else walk_observation obs rounds (S (S x)) 0))) =
      p * walk_eval rounds (fun n => f (obs n)) x (S y) +
      q * walk_eval rounds (fun n => f (obs n)) (S (S x)) 0).
    by rewrite enum_expect_bind rw_coin_expect !IH.
Qed.

Lemma walk_approx_expect rounds f x y :
  enum_expect f (subenum_raw (walk_approx rounds x y)) = walk_eval rounds f x y.
Proof. exact (walk_observation_expect (fun n => n) f rounds x y). Qed.

Local Notation radius := (3 / 2 : rat).
Local Notation contraction := (17 / 18 : rat).

Lemma rw_radius_ge_one : 1 <= radius.
Proof. native_compute. reflexivity. Qed.
Lemma rw_radius_positive : 0 < radius.
Proof. native_compute. reflexivity. Qed.
Lemma rw_contraction_nonnegative : 0 <= contraction.
Proof. native_compute. reflexivity. Qed.

Lemma walk_error_step x rounds :
  p * (radius ^+ x * contraction ^+ rounds) +
  q * (radius ^+ S (S x) * contraction ^+ rounds) =
  radius ^+ S x * contraction ^+ S rounds.
Proof. rewrite !exprS. rw_rat. field; vm_compute; intuition discriminate. Qed.

(** A bounded harmonic candidate is uniquely determined by its boundary:
    every finite execution approximation converges to it.  This argument
    rules out spurious fixed points of the renewal equation. *)
Theorem walk_harmonic_error (f : nat -> rat) (H : nat -> nat -> rat)
    (Hbound : forall x y, 0 <= H x y <= 1)
    (Hzero : forall y, H 0 y = f y)
    (Hstep : forall x y, H (S x) y = p * H x (S y) + q * H (S (S x)) 0)
    rounds x y :
  `|walk_eval rounds f x y - H x y| <= radius ^+ x * contraction ^+ rounds.
Proof.
  revert x y. induction rounds as [|rounds IH]; intros [|x] y.
  - rewrite Hzero subrr normr0 expr0 mulr1. by [].
  - change (`|0 - H (S x) y| <= radius ^+ S x * contraction ^+ 0).
    have [H0 H1] := andP (Hbound (S x) y).
    rewrite expr0 mulr1 sub0r normrN (ger0_norm H0).
    apply: le_trans H1 _. apply exprn_ege1. exact rw_radius_ge_one.
  - rewrite Hzero subrr normr0 expr0 mul1r.
    exact (exprn_ge0 _ rw_contraction_nonnegative).
  - change (`|p * walk_eval rounds f x (S y) +
      q * walk_eval rounds f (S (S x)) 0 - H (S x) y| <=
      radius ^+ S x * contraction ^+ S rounds).
    rewrite Hstep.
    have Heq : p * walk_eval rounds f x (S y) +
        q * walk_eval rounds f (S (S x)) 0 -
        (p * H x (S y) + q * H (S (S x)) 0) =
        p * (walk_eval rounds f x (S y) - H x (S y)) +
        q * (walk_eval rounds f (S (S x)) 0 - H (S (S x)) 0).
    { rw_rat. ring. }
    rewrite Heq -walk_error_step.
    apply: le_trans (ler_normD _ _) _.
    rewrite (normrM p _) (normrM q _)
      (ger0_norm rw_p_nonnegative) (ger0_norm rw_q_nonnegative).
    apply lerD.
    + exact (ler_wpM2l rw_p_nonnegative (IH x (S y))).
    + exact (ler_wpM2l rw_q_nonnegative (IH (S (S x)) 0)).
Qed.

Definition rational_limit (chain : nat -> rat) (value : rat) : Prop :=
  forall eps : rat, 0 < eps ->
  exists N, forall rounds, (N <= rounds)%coq_nat ->
    `|chain rounds - value| < eps.

Lemma walk_error_vanishes x :
  forall eps : rat, 0 < eps -> exists N, forall rounds,
    (N <= rounds)%coq_nat -> radius ^+ x * contraction ^+ rounds < eps.
Proof.
  intros eps Heps.
  have Hr : 0 < radius ^+ x := exprn_gt0 x rw_radius_positive.
  have Hdiv : 0 < eps / radius ^+ x := divr_gt0 Heps Hr.
  destruct (@rat_contract_vanishes contraction 17 ltac:(lia)
    rw_contraction_nonnegative (lexx contraction) _ Hdiv) as [N HN].
  exists N. intros rounds Hrounds.
  have H := HN rounds Hrounds.
  move: H. by rewrite ltr_pdivlMr // mulrC.
Qed.

Theorem walk_harmonic_limit (f : nat -> rat) (H : nat -> nat -> rat)
    (Hbound : forall x y, 0 <= H x y <= 1)
    (Hzero : forall y, H 0 y = f y)
    (Hstep : forall x y, H (S x) y = p * H x (S y) + q * H (S (S x)) 0)
    x y : rational_limit (fun rounds => walk_eval rounds f x y) (H x y).
Proof.
  intros eps Heps. destruct (walk_error_vanishes x Heps) as [N HN].
  exists N. intros rounds Hrounds.
  exact (le_lt_trans (walk_harmonic_error Hbound Hzero Hstep rounds x y)
    (HN rounds Hrounds)).
Qed.

Theorem walk_mass_limit x y :
  rational_limit (fun rounds => enum_mass (subenum_raw (walk_approx rounds x y))) 1.
Proof.
  unfold enum_mass, rational_limit. setoid_rewrite walk_approx_expect.
  apply (walk_harmonic_limit (H := fun _ _ => 1)).
  - by intros.
  - reflexivity.
  - intros. rw_rat. field; vm_compute; intuition discriminate.
Qed.

Theorem walk_atom_limit x y n :
  rational_limit (fun rounds => enum_expect
    (fun z => if Nat.eqb n z then 1 else 0)
    (subenum_raw (walk_approx rounds x y))) (passage_pmf x y n).
Proof.
  unfold rational_limit. setoid_rewrite walk_approx_expect.
  apply (walk_harmonic_limit (H := fun x y => passage_pmf x y n)).
  - intros. apply passage_pmf_bound.
  - intros. apply passage_pmf_zero.
  - intros. apply passage_pmf_harmonic.
Qed.

Corollary initial_walk_geometric_limit n :
  rational_limit (fun rounds => enum_expect
    (fun z => if Nat.eqb n z then 1 else 0)
    (subenum_raw (walk_approx rounds 1 0))) (geometric_pmf n).
Proof. rewrite -passage_pmf_initial. apply walk_atom_limit. Qed.

(** Link the finite calculations to the maintained primitive kernel. *)
Local Notation walk_head := (stable_head rwE SubEnum nat).

Definition walk_head_value (h : walk_head) : nat :=
  match h with
  | FHRet n => n
  | @FHVis _ _ _ X e _ => match e with end
  end.

Fixpoint walk_schedule (rounds : nat) : nat :=
  match rounds with O => O | S n => S (S (walk_schedule n)) end.

Definition walk_hitting fuel x y : FreeOmega SubEnum walk_head :=
  ptree_hitting_approx (FI := rwFI) (FO := rwFO) fuel
    (observe (@run_until_zero rwE SubEnum rw_coin x y)).

Lemma walk_hitting_two fuel x y :
  walk_hitting (S (S fuel)) (S x) y =
  FOSample rw_coin (fun down =>
    if down then walk_hitting fuel x (S y)
            else walk_hitting fuel (S (S x)) 0).
Proof.
  unfold walk_hitting at 1. rewrite run_succ_observe.
  cbn [ptree_hitting_approx ptree_primitive_kernel stable_hitting_approx
    stable_target_approx sem_bind sem_ret mixed_bind free_omega_bind
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticMeasure FreeOmegaSemanticMeasure].
  f_equal. apply functional_extensionality. intros []; reflexivity.
Qed.

Lemma walk_hitting_observes {A} (obs : nat -> A) rounds x y :
  free_omega_observes (fun h => obs (walk_head_value h))
    (walk_hitting (walk_schedule rounds) x y)
    (walk_observation obs rounds x y).
Proof.
  revert x y. induction rounds as [|rounds IH]; intros [|x] y.
  - change (free_omega_observes (fun h => obs (walk_head_value h))
      (FORet (FHRet y)) (subenum_ret (obs y))).
    constructor.
  - change (free_omega_observes (fun h => obs (walk_head_value h))
      (FOSample rw_coin (fun _ => FOZero))
      (subenum_bind rw_coin (fun _ => subenum_zero))).
    eapply (@FOOObserveSample SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticOmega) with (front := fun _ => @subenum_zero A).
    intros b. constructor.
  - change (free_omega_observes (fun h => obs (walk_head_value h))
      (FORet (FHRet y)) (subenum_ret (obs y))).
    constructor.
  - cbn [walk_schedule]. rewrite walk_hitting_two.
    change (free_omega_observes (fun h => obs (walk_head_value h))
      (FOSample rw_coin (fun down =>
        if down then walk_hitting (walk_schedule rounds) x (S y)
                else walk_hitting (walk_schedule rounds) (S (S x)) 0))
      (subenum_bind rw_coin (fun down =>
        if down then walk_observation obs rounds x (S y)
                else walk_observation obs rounds (S (S x)) 0))).
    eapply (@FOOObserveSample SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticOmega) with (front := fun down =>
      if down then walk_observation obs rounds x (S y)
              else walk_observation obs rounds (S (S x)) 0).
    intros []; apply IH.
Qed.

Lemma walk_unit_converges x y :
  subenum_sem_lub (fun rounds => walk_observation (fun _ => tt) rounds x y)
    (subenum_ret tt).
Proof.
  intros P eps Heps.
  have Hlimit : rational_limit
      (fun rounds => walk_eval rounds (fun _ => if P tt then 1 else 0) x y)
      (if P tt then 1 else 0).
  { apply (walk_harmonic_limit (H := fun _ _ => if P tt then 1 else 0)).
    - intros. destruct (P tt); by [].
    - reflexivity.
    - intros. destruct (P tt); rw_rat; field; vm_compute; intuition discriminate. }
  destruct (Hlimit eps Heps) as [N HN].
  exists N. intros rounds Hrounds.
  rewrite walk_observation_expect enum_expect_ret.
  exact (HN rounds Hrounds).
Qed.

Definition walk_limit x y :=
  FOLub (fun rounds => walk_hitting (walk_schedule rounds) x y).

Lemma walk_schedule_ge rounds : (rounds <= walk_schedule rounds)%coq_nat.
Proof. induction rounds; cbn [walk_schedule]; lia. Qed.

Lemma walk_hitting_cofinal x y :
  free_omega_chains_cofinal eq (fun fuel => walk_hitting fuel x y)
    (fun rounds => walk_hitting (walk_schedule rounds) x y).
Proof.
  split.
  - intros fuel. exists fuel.
    apply (ptree_hitting_mono (MF := FreeOmega SubEnum)
      (FI := FreeOmegaObservableSemanticMeasure
        (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
      (FO := FreeOmegaObservableSemanticOmega)).
    apply walk_schedule_ge.
  - intros rounds. exists (walk_schedule rounds).
    apply free_omega_approx_refl. intros h. reflexivity.
Qed.

Lemma walk_limit_hitting x y :
  ptree_stable_hitting (FI := rwFI) (FO := rwFO)
    (observe (@run_until_zero rwE SubEnum rw_coin x y)) (walk_limit x y).
Proof.
  unfold ptree_stable_hitting, stable_hitting, walk_limit.
  change (free_omega_qlift eq
    (FOLub (fun rounds => walk_hitting (walk_schedule rounds) x y))
    (FOLub (fun fuel => walk_hitting fuel x y))).
  apply FOQLSym. eapply FOQLMono.
  - apply FOQLCofinal.
    + intro n. unfold walk_hitting.
      apply (ptree_hitting_mono (FI := rwFI) (FO := rwFO)). lia.
    + intro n. unfold walk_hitting.
      apply (ptree_hitting_mono (FI := rwFI) (FO := rwFO)).
      cbn [walk_schedule]. lia.
    + apply walk_hitting_cofinal.
  - intros h h' ->. reflexivity.
Qed.

Lemma walk_limit_observes_unit x y :
  free_omega_observes (fun _ : walk_head => tt) (walk_limit x y) (subenum_ret tt).
Proof.
  apply FOOObserveLub with
      (outs := fun rounds => walk_observation (fun _ => tt) rounds x y).
  - intros rounds. apply (walk_hitting_observes (fun _ => tt)).
  - apply walk_unit_converges.
  - intro n. apply (ptree_hitting_mono (FI := rwFI) (FO := rwFO)).
    cbn [walk_schedule]. lia.
Qed.

Theorem walk_ast x y :
  ptree_stable_hitting_ast (FI := rwFI) (FO := rwFO)
    (observe (@run_until_zero rwE SubEnum rw_coin x y)) (walk_limit x y).
Proof.
  split; first apply walk_limit_hitting.
  apply free_omega_observable_total_intro.
  exists unit, (fun _ : walk_head => tt), (subenum_ret tt).
  split.
  - apply walk_limit_observes_unit.
  - change (enum_mass (ret_Enum tt) = 1).
    exact (enum_expect_ret (fun _ : unit => (1 : rat)) tt).
Qed.

(** Transport the same native limit through the structural splitting law.
    This connects the quantitative two-level passage to the actual bind in
    the renewal equation, rather than introducing an unrelated sampler. *)
Theorem continuation_stable_hitting_ast :
  ptree_stable_hitting_ast (FI := rwFI) (FO := rwFO)
    (observe rw_continuation) (walk_limit 2 0).
Proof.
  destruct (walk_ast 2 0) as [Hhit Htotal]. split; last exact Htotal.
  apply (proj1 (ptree_stable_hitting_pstruct_no_event
    (fun X (e : rwE X) => match e with end)
    (@height_two_split rwE SubEnum rw_coin) (walk_limit 2 0))).
  exact Hhit.
Qed.

(** The original program returns the joint state, not just the streak. *)
Local Notation joint_head := (stable_head rwE SubEnum rw_state).

Definition joint_head_value (h : joint_head) : rw_state :=
  match h with
  | FHRet s => s
  | @FHVis _ _ _ X e _ => match e with end
  end.

Definition joint_hitting fuel x y : FreeOmega SubEnum joint_head :=
  ptree_hitting_approx (FI := rwFI) (FO := rwFO) fuel
    (observe (PTree.iter (rw_body rw_coin) (x,y))).

Lemma joint_hitting_two fuel x y :
  joint_hitting (S (S fuel)) (S x) y =
  FOSample rw_coin (fun down =>
    if down then joint_hitting fuel x (S y)
            else joint_hitting fuel (S (S x)) 0).
Proof.
  have Hobs : observe (PTree.iter (@rw_body rwE SubEnum rw_coin) (S x,y)) =
    ProbF rw_coin (fun down => PTree.bind (Ret (inl (rw_next x y down)))
      (fun next : rw_state + rw_state =>
        match next with
        | inl s => Tau (PTree.iter (rw_body rw_coin) s)
        | inr s => Ret s
        end)) by reflexivity.
  unfold joint_hitting at 1. rewrite Hobs.
  cbn [ptree_hitting_approx ptree_primitive_kernel stable_hitting_approx
    stable_target_approx sem_bind sem_ret mixed_bind free_omega_bind
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticMeasure FreeOmegaSemanticMeasure].
  f_equal. apply functional_extensionality. intros []; reflexivity.
Qed.

Lemma joint_hitting_observes {A} (obs : rw_state -> A) rounds x y :
  free_omega_observes (fun h => obs (joint_head_value h))
    (joint_hitting (walk_schedule rounds) x y)
    (walk_observation (fun n => obs (0%nat,n)) rounds x y).
Proof.
  revert x y. induction rounds as [|rounds IH]; intros [|x] y.
  - change (free_omega_observes (fun h => obs (joint_head_value h))
      (FORet (FHRet (0%nat,y))) (subenum_ret (obs (0%nat,y)))).
    constructor.
  - change (free_omega_observes (fun h => obs (joint_head_value h))
      (FOSample rw_coin (fun _ => FOZero))
      (subenum_bind rw_coin (fun _ => subenum_zero))).
    eapply (@FOOObserveSample SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticOmega) with (front := fun _ => @subenum_zero A).
    intros b. constructor.
  - change (free_omega_observes (fun h => obs (joint_head_value h))
      (FORet (FHRet (0%nat,y))) (subenum_ret (obs (0%nat,y)))).
    constructor.
  - cbn [walk_schedule]. rewrite joint_hitting_two.
    change (free_omega_observes (fun h => obs (joint_head_value h))
      (FOSample rw_coin (fun down =>
        if down then joint_hitting (walk_schedule rounds) x (S y)
                else joint_hitting (walk_schedule rounds) (S (S x)) 0))
      (subenum_bind rw_coin (fun down =>
        if down then walk_observation (fun n => obs (0%nat,n)) rounds x (S y)
                else walk_observation (fun n => obs (0%nat,n)) rounds (S (S x)) 0))).
    eapply (@FOOObserveSample SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticOmega) with (front := fun down =>
      if down then walk_observation (fun n => obs (0%nat,n)) rounds x (S y)
              else walk_observation (fun n => obs (0%nat,n)) rounds (S (S x)) 0).
    intros []; apply IH.
Qed.

Definition random_walk_heads :=
  FOLub (fun rounds => joint_hitting (walk_schedule rounds) 1 0).

Theorem random_walk_ast :
  ptree_stable_hitting_ast (FI := rwFI) (FO := rwFO)
    (observe random_walk) random_walk_heads.
Proof.
  split.
  - unfold ptree_stable_hitting, stable_hitting, random_walk_heads.
    change (free_omega_qlift eq
      (FOLub (fun rounds => joint_hitting (walk_schedule rounds) 1 0))
      (FOLub (fun fuel => joint_hitting fuel 1 0))).
    apply FOQLSym. eapply FOQLMono.
    + apply FOQLCofinal.
      { intro n. unfold joint_hitting.
        apply (ptree_hitting_mono (FI := rwFI) (FO := rwFO)). lia. }
      { intro n. unfold joint_hitting.
        apply (ptree_hitting_mono (FI := rwFI) (FO := rwFO)).
        cbn [walk_schedule]. lia. }
      split.
      * intros fuel. exists fuel.
        apply (ptree_hitting_mono (MF := FreeOmega SubEnum)
          (FI := FreeOmegaObservableSemanticMeasure
            (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
          (FO := FreeOmegaObservableSemanticOmega)).
        apply walk_schedule_ge.
      * intros rounds. exists (walk_schedule rounds).
        apply free_omega_approx_refl. intros h. reflexivity.
    + intros h h' ->. reflexivity.
  - apply free_omega_observable_total_intro.
    exists unit, (fun _ : joint_head => tt), (subenum_ret tt).
    split.
    + apply FOOObserveLub with
        (outs := fun rounds => walk_observation (fun _ => tt) rounds 1 0).
      * intros rounds. apply (joint_hitting_observes (fun _ => tt)).
      * apply walk_unit_converges.
      * intro n. apply (ptree_hitting_mono (FI := rwFI) (FO := rwFO)).
        cbn [walk_schedule]. lia.
    + change (enum_mass (ret_Enum tt) = 1).
      exact (enum_expect_ret (fun _ : unit => (1 : rat)) tt).
Qed.

Definition random_walk_outputs rounds : SubEnum rw_state :=
  walk_observation (fun n => (0%nat,n)) rounds 1 0.

Lemma random_walk_outputs_spec rounds :
  free_omega_observes joint_head_value
    (joint_hitting (walk_schedule rounds) 1 0) (random_walk_outputs rounds).
Proof. apply (joint_hitting_observes (fun s => s)). Qed.

Definition state_indicator (s t : rw_state) : rat :=
  if Nat.eqb (fst s) (fst t) && Nat.eqb (snd s) (snd t) then 1 else 0.

(** A joint distribution theorem about observations of the *source* kernel.
    This is not a converse from pointwise probability equality to [peutt]. *)
Theorem random_walk_output_dist s :
  rational_limit (fun rounds =>
    enum_expect (state_indicator s) (subenum_raw (random_walk_outputs rounds)))
    (joint_pmf s).
Proof.
  unfold random_walk_outputs, rational_limit.
  setoid_rewrite walk_observation_expect.
  destruct s as [[|x] n].
  - change (rational_limit
      (fun rounds => walk_eval rounds (fun z => if Nat.eqb n z then 1 else 0) 1 0)
      (geometric_pmf n)).
    rewrite -passage_pmf_initial.
    apply (walk_harmonic_limit (H := fun x y => passage_pmf x y n)).
    + intros. apply passage_pmf_bound.
    + intros. apply passage_pmf_zero.
    + intros. apply passage_pmf_harmonic.
  - change (rational_limit (fun rounds => walk_eval rounds (fun _ => 0) 1 0) 0).
    apply (walk_harmonic_limit (H := fun _ _ => 0)).
    + by intros.
    + reflexivity.
    + intros. by rewrite !mulr0 addr0.
Qed.

Lemma joint_pmf_formula n :
  joint_pmf (0%nat, S n) = p * q ^+ n.
Proof. reflexivity. Qed.

Lemma joint_pmf_power n : joint_pmf (0%nat, S n) = 2 / (3 : rat) ^+ S n.
Proof.
  by rewrite joint_pmf_formula expr_div_n expr1n mul1r exprS invfM mulrA.
Qed.

Corollary random_walk_joint_probability n :
  rational_limit (fun rounds => enum_expect (state_indicator (0%nat, S n))
    (subenum_raw (random_walk_outputs rounds))) (2 / (3 : rat) ^+ S n).
Proof. rewrite -joint_pmf_power. apply random_walk_output_dist. Qed.

Lemma joint_pmf_x_nonzero x y :
  x <> 0%nat -> joint_pmf (x,y) = 0.
Proof. destruct x; [contradiction|reflexivity]. Qed.

Lemma joint_pmf_y_zero : joint_pmf (0%nat,0%nat) = 0.
Proof. reflexivity. Qed.

(** [height_two_split] identifies this two-level passage with
    [rw_D0 >>= rw_passage].  Its limiting PMF is the successor pushforward
    of [rw_D0]; subtraction at zero is harmless since [geometric_pmf 0 = 0]. *)
Lemma continuation_pmf n :
  passage_pmf 2 0 n = geometric_pmf (n-1)%nat.
Proof.
  rewrite passage_pmf_reset expr1.
  change ((0 + q * 1 * geometric_pmf (n-1)%nat) +
    p * geometric_pmf (n-1)%nat = geometric_pmf (n-1)%nat).
  rw_rat. field; vm_compute; intuition discriminate.
Qed.

Corollary continuation_output_limit n :
  rational_limit (fun rounds => enum_expect
    (fun z => if Nat.eqb n z then 1 else 0)
    (subenum_raw (walk_approx rounds 2 0))) (geometric_pmf (n-1)%nat).
Proof. rewrite -continuation_pmf. apply walk_atom_limit. Qed.

Lemma D0_geometric_equation n :
  geometric_pmf n = p * (if Nat.eqb n 1 then 1 else 0) +
    q * geometric_pmf (n-1)%nat.
Proof. have H := geometric_recurrence n 0. by rewrite subn0 in H. Qed.

(** Normalization is a limit of finite sums, not an infinite list in Enum. *)
Fixpoint geometric_partial_mass (length : nat) : rat :=
  match length with
  | O => 0
  | S n => geometric_partial_mass n + geometric_pmf (S n)
  end.

Lemma geometric_partial_mass_formula length :
  geometric_partial_mass length = 1 - q ^+ length.
Proof.
  induction length as [|length IH]; first by rewrite expr0 subrr.
  change (geometric_partial_mass length + p * q ^+ length = 1 - q ^+ S length).
  rewrite IH exprS. rw_rat. field; vm_compute; intuition discriminate.
Qed.

Lemma joint_pmf_normalized : rational_limit geometric_partial_mass 1.
Proof.
  intros eps Heps.
  have Hq : q <= (1 : rat) / 2 by native_compute.
  destruct (@rat_contract_vanishes q 1 ltac:(lia) rw_q_nonnegative Hq eps Heps)
    as [N HN].
  exists N. intros rounds Hrounds.
  rewrite geometric_partial_mass_formula addrAC subrr add0r normrN
    (ger0_norm (exprn_ge0 rounds rw_q_nonnegative)).
  exact (HN rounds Hrounds).
Qed.

(** The completed endpoint combines the native AST certificate with the
    exact finite observations and their normalized closed-form limit.
    It does not assert an unproved distribution-to-bisimulation converse. *)
Theorem random_walk_closed_form :
  ptree_stable_hitting_ast (FI := rwFI) (FO := rwFO)
    (observe random_walk) random_walk_heads /\
  (forall rounds, free_omega_observes joint_head_value
    (joint_hitting (walk_schedule rounds) 1 0) (random_walk_outputs rounds)) /\
  (forall s, rational_limit (fun rounds => enum_expect (state_indicator s)
    (subenum_raw (random_walk_outputs rounds))) (joint_pmf s)) /\
  rational_limit geometric_partial_mass 1.
Proof.
  split; first exact random_walk_ast.
  split; first exact random_walk_outputs_spec.
  split; [exact random_walk_output_dist|exact joint_pmf_normalized].
Qed.

(** Regression: three rounds do not yet realize the limiting second atom.
    The extra mass 2/9 - 4/27 is contributed by genuinely longer paths. *)
Example random_walk_three_rounds_second_atom :
  enum_expect (state_indicator (0%nat,2%nat))
    (subenum_raw (random_walk_outputs 3)) = 4 / 27.
Proof. native_compute. reflexivity. Qed.

Example random_walk_limiting_second_atom : joint_pmf (0%nat,2%nat) = 2 / 9.
Proof. native_compute. reflexivity. Qed.
