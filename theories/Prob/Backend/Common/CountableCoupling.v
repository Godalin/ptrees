(** External validation: decode nat transport to arbitrary countably
    supported carriers. Neither carrier needs a countable/inhabited structure. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect reals.
From PTree.Prob.Domain Require Import Expectation Countable Coupling CountableTransport.
From PTree.Prob.Backend.Common Require Import DomainTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Realization.
Variable R : realType.

(** The supplied covers may repeat values and contain invalid codes. The
    coded relation itself ensures that decoding loses no positive mass. *)
Theorem oval_bidual_coupled_on_enumerations {A B} (T : A -> B -> Prop)
    (L : OmegaVal R A) (M : OmegaVal R B) e d :
  oval_ae L (oval_enumerated e) -> oval_ae M (oval_enumerated d) ->
  oval_bidual T L M -> oval_coupled T L M.
Proof.
  intros HL HM HT.
  destruct (oval_bidual_coupled_nat (oval_coded_bidual HL HM HT)) as [J HJ].
  exists (oval_bind J (oval_pair_decode R e d)).
  exact (oval_joint_decode (oval_coded_representation HL) (oval_coded_representation HM) HJ).
Qed.

Theorem oval_bidual_coupled {A B} (T : A -> B -> Prop)
    (L : OmegaVal R A) (M : OmegaVal R B) :
  oval_countably_supported L -> oval_countably_supported M ->
  oval_bidual T L M -> oval_coupled T L M.
Proof.
  intros HL HM HT.
  destruct (oval_countable_transport_reduction HL HM HT)
    as [e [d [N [K [HN [HK [Hdual Hdecode]]]]]]].
  destruct (oval_bidual_coupled_nat Hdual) as [J HJ].
  exists (oval_bind J (oval_pair_decode R e d)); exact (Hdecode J HJ).
Qed.

(** This is dual/joint equivalence in the external model, NOT completeness
    of FreeOmega's syntactic qlift. *)
Theorem oval_countable_coupling_iff {A B} (T : A -> B -> Prop)
    (L : OmegaVal R A) (M : OmegaVal R B) :
  oval_countably_supported L -> oval_countably_supported M ->
  (oval_bidual T L M <-> oval_coupled T L M).
Proof.
  intros HL HM; split; first exact (oval_bidual_coupled HL HM).
  intros [J HJ]; exact (oval_joint_dual HJ).
Qed.
End Realization.
