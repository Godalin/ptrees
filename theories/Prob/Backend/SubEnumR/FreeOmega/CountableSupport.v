(** Backend-specific external validation: raw finite-real completion syntax
    has an enumerable cover, independently of modelability. Only modelable
    endpoints induce countably supported OmegaVal values. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype choice ssrnat ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import StructuralMeasure.
From PTree.Prob.FreeOmega.Validation Require Import Expectation.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Domain.
From PTree.Prob.Backend.SubEnumR.FreeOmega Require Import Validation.
From PTree.Prob.Domain Require Import Expectation Countable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CountableSupport.
Variable R : realType.
Local Notation native := (fun X => @subenumR_domain R X).

Fixpoint subenumR_free_omega_enumerate {A}
    (t : FreeOmega (SubEnumR R) A) (n : nat) : option A :=
  match t with
  | FORet x => Some x
  | FOZero => None
  | @FOSample _ _ X mu k =>
      match (@unpickle _ n : option (nat * nat)) with
      | Some (i,j) =>
          match List.nth_error (subenumR_raw mu) i with
          | Some (_,x) => subenumR_free_omega_enumerate (k x) j
          | None => None
          end
      | None => None
      end
  | FOLub c =>
      match (@unpickle _ n : option (nat * nat)) with
      | Some (i,j) => subenumR_free_omega_enumerate (c i) j
      | None => None
      end
  end.

Theorem subenumR_free_omega_enumerate_covers {A}
    (t : FreeOmega (SubEnumR R) A) :
  free_omega_ae (oval_enumerated (subenumR_free_omega_enumerate t)) t.
Proof.
  induction t as [x| |X mu k IH|c IH].
  - apply FOAERet; exists O; reflexivity.
  - apply FOAEZero.
  - apply FOAESample with (Good := fun x => exists w, List.In (w,x) (subenumR_raw mu)).
    + intros w x Hin _; exists w; exact Hin.
    + intros x [w Hin]. apply List.In_nth_error in Hin; destruct Hin as [i Hi].
      eapply free_omega_ae_mono; [|exact (IH x)].
      intros y [j Hj]; exists (pickle (i,j)).
      cbn [subenumR_free_omega_enumerate]; rewrite pickleK Hi; exact Hj.
  - apply FOAELub=> i; eapply free_omega_ae_mono; [|exact (IH i)].
    intros y [j Hj]; exists (pickle (i,j)).
    cbn [subenumR_free_omega_enumerate]; rewrite pickleK; exact Hj.
Qed.

Theorem subenumR_free_omega_model_enumerated {A}
    (t : FreeOmega (SubEnumR R) A) (Ht : free_omega_modelable native t) :
  oval_ae (free_omega_model Ht)
    (oval_enumerated (subenumR_free_omega_enumerate t)).
Proof.
  intros f g Hf Hg Hfg.
  apply (model_upper_ae_ext (@subenumR_native_model_ae R)); [exact Hf|exact Hg|].
  eapply free_omega_ae_mono; [|exact (subenumR_free_omega_enumerate_covers t)].
  exact Hfg.
Qed.

Theorem subenumR_free_omega_model_countable {A}
    (t : FreeOmega (SubEnumR R) A) (Ht : free_omega_modelable native t) :
  oval_countably_supported (free_omega_model Ht).
Proof.
  exists (subenumR_free_omega_enumerate t).
  exact: subenumR_free_omega_model_enumerated.
Qed.
End CountableSupport.
