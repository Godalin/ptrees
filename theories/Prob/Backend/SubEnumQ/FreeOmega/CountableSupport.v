(** Role: External validation of countable support. Even raw formal Lubs
    have an enumerable support cover; only admissible endpoints are packaged
    as probability objects. The cover is not claimed minimal or injective. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype choice ssrnat ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import StructuralMeasure.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import Admissibility UpperCoupling.
From PTree.Prob.Domain Require Import Expectation Countable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint free_omega_enumerate {A} (t : FreeOmega SubEnumQ A) (n : nat) : option A :=
  match t with
  | FORet x => Some x
  | FOZero => None
  | @FOSample _ _ X mu k =>
      match (@unpickle _ n : option (nat * nat)) with
      | Some (i,j) =>
          match List.nth_error (subenumQ_raw mu) i with
          | Some (_,x) => free_omega_enumerate (k x) j
          | None => None
          end
      | None => None
      end
  | FOLub c =>
      match (@unpickle _ n : option (nat * nat)) with
      | Some (i,j) => free_omega_enumerate (c i) j
      | None => None
      end
  end.

Theorem free_omega_enumerate_covers {A} (t : FreeOmega SubEnumQ A) :
  free_omega_ae (oval_enumerated (free_omega_enumerate t)) t.
Proof.
  induction t as [x| |X mu k IH|c IH].
  - apply FOAERet; exists O; reflexivity.
  - apply FOAEZero.
  - apply FOAESample with (Good := fun x => exists w, List.In (w,x) (subenumQ_raw mu)).
    + intros w x Hin _; exists w; exact Hin.
    + intros x [w Hin]. apply List.In_nth_error in Hin; destruct Hin as [i Hi].
      eapply free_omega_ae_mono; [|exact (IH x)].
      intros y [j Hj]; exists (pickle (i,j)).
      cbn [free_omega_enumerate]; rewrite pickleK Hi; exact Hj.
  - apply FOAELub=> i; eapply free_omega_ae_mono; [|exact (IH i)].
    intros y [j Hj]; exists (pickle (i,j)).
    cbn [free_omega_enumerate]; rewrite pickleK; exact Hj.
Qed.

Section Interpretation.
Variable R : realType.

Theorem free_omega_domain_enumerated {A} (t : FreeOmega SubEnumQ A)
    (H : free_omega_admissible R t) :
  oval_ae (free_omega_domain H) (oval_enumerated (free_omega_enumerate t)).
Proof.
  intros f g Hf Hg Hfg; apply free_omega_upper_ae_ext; [exact Hf|exact Hg|].
  eapply free_omega_ae_mono; [|exact (free_omega_enumerate_covers t)].
  exact Hfg.
Qed.

Theorem free_omega_domain_countable {A} (t : FreeOmega SubEnumQ A)
    (H : free_omega_admissible R t) : oval_countably_supported (free_omega_domain H).
Proof. exists (free_omega_enumerate t); exact: free_omega_domain_enumerated. Qed.

Theorem free_omega_domain_countable_representation {A} (t : FreeOmega SubEnumQ A)
    (H : free_omega_admissible R t) :
  exists N : OmegaVal R nat,
    oval_mass N = oval_mass (free_omega_domain H) /\
    oval_ae N (fun n => exists x, free_omega_enumerate t n = Some x) /\
    oval_eq (free_omega_domain H)
      (oval_bind N (oval_decode R (free_omega_enumerate t))).
Proof. apply oval_countable_representation; exact: free_omega_domain_enumerated. Qed.
End Interpretation.
