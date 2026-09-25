(** External validation endpoint: raw quotient lifting reflects to an actual
    finite native joint. This consumes scalar validation, NOT an external
    joint, and must not be imported by maintained behavioral theory.
    The existing capability is returned explicitly, never registered globally. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import SemanticCoupling.
From PTree.Prob.FreeOmega Require Import Quotient Native NativeCoupling.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling FiniteTransport Domain Omega.
From PTree.Prob.Backend.SubEnumR.FreeOmega Require Import RelationalValidation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section NativeReflection.
Variable R : realType.

Theorem subenumR_native_quotient_coupling {A B}
    (p : free_omega_native_presentation (SubEnumR R) A)
    (q : free_omega_native_presentation (SubEnumR R) B) (T : A -> B -> Prop) :
  free_omega_qlift T (free_omega_native p) (free_omega_native q) ->
  exists joint : SubEnumR R (native_sample_type p * native_sample_type q),
    @semantic_coupling (SubEnumR R) (SubEnumR_SemanticMeasure R) _ _
      (fun x y => T (native_sample_value p x) (native_sample_value q y))
      (native_sample_measure p) (native_sample_measure q) joint.
Proof.
  intro H; destruct (subenumR_qlift_bidual_raw H) as [Hl Hr].
  apply subenumR_lift_realization.
  apply subenumR_transport_of_mapped_tests.
  - intros f g Hf Hg Hfg; exact (Hl f g Hf Hg Hfg).
  - apply/eqP; rewrite eq_le; apply/andP; split.
    + exact (Hl (fun _ => 1) (fun _ => 1)
        (fun _ => conj ler01 (lexx _))
        (fun _ => conj ler01 (lexx _)) (fun _ _ _ => lexx _)).
    + exact (Hr (fun _ => 1) (fun _ => 1)
        (fun _ => conj ler01 (lexx _))
        (fun _ => conj ler01 (lexx _)) (fun _ _ _ => lexx _)).
Qed.

Definition subenumR_validated_native_coupling :
  @FreeOmegaNativeCouplingLaws (SubEnumR R)
    (SubEnumR_SemanticMeasure R) (SubEnumR_SemanticOmega R).
Proof. constructor; intros; exact: subenumR_native_quotient_coupling. Qed.
End NativeReflection.
