(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From Coq.Program Require Import Equality.
From mathcomp Require Import ssralg ssrnum rat.
From PTree.Prob.Backend Require Import RatSubTypes DiscreteMC.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.Backend Require Import TwoLevelMeasureEnum TwoLevelMeasureSubEnum MeasureIterationEnum.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Examples Require Import RandomWalk.
Import Enum.
Local Open Scope ring_scope.

(** Regressions for the monotonicity premises of the FreeOmega limit
    rules.  These are rule-boundary tests, not a denotational soundness
    theorem for every constructor of [free_omega_qlift]. *)
Module LimitSafety.

Definition big : FreeOmega Enum unit :=
  FOSample rw_coin_raw (fun _ => FORet tt).
Definition small : FreeOmega Enum unit :=
  FOSample rw_coin_raw (fun b : bool => if b then FORet tt else FOZero).
Definition dropping n := match n with O => big | S _ => small end.

Definition big_out : Enum unit := sem_bind rw_coin_raw (fun _ => sem_ret tt).
Definition small_out : Enum unit := sem_bind rw_coin_raw
  (fun b : bool => if b then sem_ret tt else sem_zero).

Example source_is_subprobability : enum_subprob rw_coin_raw.
Proof. exact rw_coin_subprob. Qed.

Example different_masses :
  enum_expect (fun _ => 1) big_out <> enum_expect (fun _ => 1) small_out.
Proof. vm_compute. discriminate. Qed.

Example big_mass_one : enum_expect (fun _ => 1) big_out = 1.
Proof. vm_compute. reflexivity. Qed.

Example small_mass_two_thirds : enum_expect (fun _ => 1) small_out = 2 / 3.
Proof. vm_compute. reflexivity. Qed.

Lemma small_below_big : free_omega_approx eq small big.
Proof.
  apply FOApproxSample with (S := eq).
  - apply sem_lift_refl. intro b. reflexivity.
  - intros [] y <-; [apply FOApproxRet; reflexivity|apply FOApproxZero].
Qed.

(** This old side condition really holds, despite the invalid drop. *)
Lemma dropping_cofinal_constant :
  free_omega_chains_cofinal eq dropping (fun _ => big).
Proof.
  split.
  - intros [|n]; exists O.
    + apply free_omega_approx_refl. intro x. reflexivity.
    + apply small_below_big.
  - intro n. exists O. apply free_omega_approx_refl. intro x. reflexivity.
Qed.

Lemma big_not_below_small : ~ free_omega_approx eq big small.
Proof.
  intro H. unfold big, small in H. dependent destruction H.
  pose proof (sem_lift_ae_transport_r H
    (sem_ae_true rw_coin_raw)) as Hsupport.
  assert (Hnonzero : rw_up_weight <> nnQ_0).
  { intro Hz. apply (f_equal Qval) in Hz.
    change ((1 / 3 : rat) = 0) in Hz. vm_compute in Hz. discriminate. }
  destruct (Hsupport rw_up_weight false (or_intror (or_introl eq_refl))
    Hnonzero) as [x [Hxy _]].
  specialize (H0 x false Hxy). dependent destruction H0.
Qed.

Lemma dropping_not_increasing :
  ~ (forall n, free_omega_approx eq (dropping n) (dropping (S n))).
Proof. intro H. exact (big_not_below_small (H O)). Qed.

Definition moving_source n : FreeOmega Enum nat := FORet n.
Definition moving_kernel x n := if Nat.eqb x n then big else small.

Lemma moving_source_not_increasing :
  ~ (forall n, free_omega_approx eq
      (moving_source n) (moving_source (S n))).
Proof.
  intro H. specialize (H O). unfold moving_source in H.
  dependent destruction H.
Qed.

Lemma moving_kernel_not_increasing :
  ~ (forall x n, free_omega_approx eq
      (moving_kernel x n) (moving_kernel x (S n))).
Proof. intro H. exact (big_not_below_small (H O O)). Qed.

(** A cofinality certificate alone must no longer apply the rule. *)
Example cofinality_alone_is_not_a_limit_rule
    (Hcofinal : free_omega_chains_cofinal eq dropping (fun _ => big)) : True.
Proof.
  Fail pose proof (FOQLCofinal Hcofinal).
  exact I.
Qed.

Example support_and_limits_alone_do_not_diagonalize
    (source_out : FreeOmega Enum nat)
    (kernel_out : nat -> FreeOmega Enum unit)
    (Hsource : free_omega_qlift eq source_out (FOLub moving_source))
    (Hkernels : forall x, free_omega_qlift eq
      (kernel_out x) (FOLub (moving_kernel x)))
    (Hsupport : free_omega_support_lift eq
      (free_omega_bind source_out kernel_out)
      (FOLub (fun n => free_omega_bind (moving_source n)
        (fun x => moving_kernel x n)))) : True.
Proof.
  Fail pose proof (FOQLBindLub Hsource Hkernels Hsupport).
  exact I.
Qed.

Example pointwise_limits_alone_do_not_integrate
    (chain : bool -> nat -> FreeOmega Enum unit)
    (out : bool -> FreeOmega Enum unit)
    (Hlim : forall x, True -> free_omega_qlift eq (out x) (FOLub (chain x))) :
    True.
Proof.
  Fail pose proof (FOQLSampleLub (sem_ae_true rw_coin_raw) Hlim).
  exact I.
Qed.

End LimitSafety.
