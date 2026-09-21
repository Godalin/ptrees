(** DS5a.2 preparation: atomic series and code/decode transport.
    No regression claims general Hall/dual-to-joint existence. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype ssralg ssrnum bigop order reals boolp.
From PTree.Prob.Domain Require Import Expectation Countable Coupling Atomic
  Series CountableTransport.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Core.PTreeDefinition.ptree.
Fail Check PTree.Prob.Domain.MeasureModel.oval_probability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section IndependentTests.
Variable R : realType.

(** No finite-support or total-mass premise: applies to every distribution
    on nat, including genuinely infinite supports and missing mass. *)
Example successor_plan (L : OmegaVal R nat) :
  oval_joint (fun i j => j = i.+1) L
    (oval_bind L (fun i => oval_ret R i.+1))
    (oval_bind (oval_series (fun i => proj1 (oval_atom_bounds L i))
      (oval_atoms_summable L)) (fun i => oval_ret R (i,i.+1))).
Proof.
  apply oval_transport_plan_joint.
  - intro x; exact (oval_series_roundtrip L (oval_singleton_test R x)).
  - intro y; apply oval_series_roundtrip.
    intro i; case: (i.+1 == y); [exact: oval_test_one|exact: oval_test_zero].
  - intros; reflexivity.
Qed.

Example subprobability_tail_is_actual_mass (L : OmegaVal R nat) eps :
  0 < eps -> exists n,
    oval_eval L (fun i => if (n <= i)%N then 1 else 0) < eps.
Proof.
  intro H; destruct (oval_atomic_tight L H) as [n Hn].
  exists n; by rewrite oval_atomic_tail.
Qed.

(** Duplicated entries and invalid codes are both intentional. *)
Definition repeated_unit n : option unit :=
  match n with O => None | _ => Some tt end.
Definition repeated_bool n : option bool :=
  match n with O => None | _ => Some true end.

Example duplicate_decode_joint :
  oval_joint (fun (_ : unit) b => b = true)
    (oval_ret R tt) (oval_ret R true)
    (oval_bind (oval_ret R (2%N,3%N))
      (oval_pair_decode R repeated_unit repeated_bool)).
Proof.
  apply (@oval_joint_decode R unit bool (fun _ b => b = true)
    (oval_ret R tt) (oval_ret R true) repeated_unit repeated_bool
    (oval_ret R 2%N) (oval_ret R 3%N) (oval_ret R (2%N,3%N))).
  - intros f Hf; reflexivity.
  - intros f Hf; reflexivity.
  - split; first by intros.
    split; first by intros.
    intros f g Hf Hg Hfg; apply (Hfg (2%N,3%N)).
    exists tt, true; repeat split.
Qed.

Example invalid_code_not_supported j :
  ~ oval_code_relation repeated_unit repeated_bool (fun _ _ => True) O j.
Proof. intros [x [y [H _]]]; discriminate H. Qed.

Example duplicate_codes_not_injective :
  repeated_unit 2%N = repeated_unit 3%N /\ 2%N <> 3%N.
Proof. split; [reflexivity|discriminate]. Qed.

(** A joint with any subprobability mass survives decoding unchanged. *)
Example decode_preserves_missing_mass (L : OmegaVal R nat) :
  oval_joint (fun (_ : unit) b => b = true)
    (oval_bind L (fun _ => oval_ret R tt))
    (oval_bind L (fun _ => oval_ret R true))
    (oval_bind (oval_bind L (fun _ => oval_ret R (2%N,3%N)))
      (oval_pair_decode R repeated_unit repeated_bool)).
Proof.
  apply (@oval_joint_decode R unit bool (fun _ b => b = true)
    (oval_bind L (fun _ => oval_ret R tt))
    (oval_bind L (fun _ => oval_ret R true)) repeated_unit repeated_bool
    (oval_bind L (fun _ => oval_ret R 2%N))
    (oval_bind L (fun _ => oval_ret R 3%N))
    (oval_bind L (fun _ => oval_ret R (2%N,3%N)))).
  - intros f Hf; reflexivity.
  - intros f Hf; reflexivity.
  - split; first by intros.
    split; first by intros.
    intros f g Hf Hg Hfg.
    change (oval_eval L (fun _ => f (2%N,3%N)) = oval_eval L (fun _ => g (2%N,3%N))).
    apply oval_eval_ext=> i; apply (Hfg (2%N,3%N)).
    exists tt, true; repeat split.
Qed.

Example duplicated_cover_dual :
  oval_bidual (oval_code_relation repeated_unit repeated_bool (fun (_ : unit) b => b = true))
    (oval_coded (oval_ret R tt) repeated_unit)
    (oval_coded (oval_ret R true) repeated_bool).
Proof.
  apply oval_coded_bidual.
  - intros f g Hf Hg Hfg; apply Hfg; exists 1%N; reflexivity.
  - intros f g Hf Hg Hfg; apply Hfg; exists 1%N; reflexivity.
  - apply (@oval_joint_dual R unit bool (fun _ b => b = true)
      (oval_ret R tt) (oval_ret R true) (oval_ret R (tt,true))).
    split; first by intros.
    split; first by intros.
    intros f g Hf Hg Hfg; apply (Hfg (tt,true)); reflexivity.
Qed.

Example zero_decoded_joint :
  oval_joint (fun (_ : Empty_set) (_ : bool) => False)
    (oval_bottom R) (oval_bottom R)
    (oval_bind (@oval_bottom R (nat * nat))
      (oval_pair_decode R (fun _ => @None Empty_set) repeated_bool)).
Proof. split; first by intros. split; first by intros. intros f g Hf Hg Hfg; reflexivity. Qed.

Example atoms_determine_measure (L M : OmegaVal R nat) :
  (forall i, oval_atom L i = oval_atom M i) -> oval_eq L M.
Proof. exact: oval_atomic_ext. Qed.
End IndependentTests.

(** Integration with the previous increment's infinite retry example. The
    transport construction remains independent of all FreeOmega machinery. *)
From PTree.Prob.Backend.SubEnum.FreeOmega Require Import Admissibility.
From PTree.Regression.Probability Require Import FreeOmegaRelationalDomain.

Example geometric_successor_plan (R : realType) :
  let L := free_omega_domain (geometric_valid R) in
  oval_joint (fun i j => j = i.+1) L
    (oval_bind L (fun i => oval_ret R i.+1))
    (oval_bind (oval_series (fun i => proj1 (oval_atom_bounds L i))
      (oval_atoms_summable L)) (fun i => oval_ret R (i,i.+1))).
Proof. apply successor_plan. Qed.
