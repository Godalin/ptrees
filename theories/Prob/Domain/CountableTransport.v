(** Role: Reduce countably supported relational transport to natural-number
    marginals and decode an actual joint. No countable transport existence
    theorem is assumed here: existence on nat remains a separate obligation. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals boolp.
From PTree.Prob.Domain Require Import Expectation Countable Coupling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Transport.
Variable R : realType.

Lemma oval_dual_ae_restrict {A B} (T : A -> B -> Prop)
    (L : OmegaVal R A) (M : OmegaVal R B) P Q :
  oval_ae L P -> oval_ae M Q -> oval_dual T L M ->
  oval_dual (fun x y => T x y /\ P x /\ Q y) L M.
Proof.
  intros HP HQ HT f g Hf Hg Hfg.
  pose f' x := if pselect (P x) then f x else 0.
  pose g' y := if pselect (Q y) then g y else 1.
  have Hf' : oval_test f'.
  { intro x; unfold f'; destruct (pselect (P x)); [exact: Hf|exact: oval_test_zero]. }
  have Hg' : oval_test g'.
  { intro y; unfold g'; destruct (pselect (Q y)); [exact: Hg|exact: oval_test_one]. }
  have Ef : oval_eval L f = oval_eval L f'.
  { apply HP; auto. intros x Hx; unfold f'; destruct (pselect (P x)); [reflexivity|contradiction]. }
  have Eg : oval_eval M g = oval_eval M g'.
  { apply HQ; auto. intros y Hy; unfold g'; destruct (pselect (Q y)); [reflexivity|contradiction]. }
  rewrite Ef Eg; apply HT; auto.
  intros x y Hxy; unfold f', g'.
  destruct (pselect (P x)) as [Hx|Hx]; destruct (pselect (Q y)) as [Hy|Hy].
  - apply Hfg; auto.
  - exact (proj2 (Hf x)).
  - exact (proj1 (Hg y)).
  - exact: ler01.
Qed.

Definition oval_coded {A} (L : OmegaVal R A) (e : nat -> option A) :=
  oval_bind L (fun x => oval_ret R (oval_code e x)).

Definition oval_code_relation {A B} (e : nat -> option A)
    (d : nat -> option B) (T : A -> B -> Prop) i j :=
  exists x y, e i = Some x /\ d j = Some y /\ T x y.

Lemma oval_coded_mass {A} (L : OmegaVal R A) e :
  oval_mass (oval_coded L e) = oval_mass L.
Proof. reflexivity. Qed.

Lemma oval_coded_representation {A} (L : OmegaVal R A) e :
  oval_ae L (oval_enumerated e) ->
  oval_eq L (oval_bind (oval_coded L e) (oval_decode R e)).
Proof.
  intros H f Hf; apply H; first exact Hf.
  - intro x; exact (oval_eval_bounds (oval_decode R e (oval_code e x)) Hf).
  - intros x Hx; change (f x = oval_eval (oval_decode R e (oval_code e x)) f).
    rewrite /oval_decode (oval_code_spec Hx); reflexivity.
Qed.

Lemma oval_coded_dual {A B} (T : A -> B -> Prop)
    (L : OmegaVal R A) (M : OmegaVal R B) e d :
  oval_ae L (oval_enumerated e) -> oval_ae M (oval_enumerated d) ->
  oval_dual T L M ->
  oval_dual (oval_code_relation e d T) (oval_coded L e) (oval_coded M d).
Proof.
  intros HL HM HT f g Hf Hg Hfg.
  apply (oval_dual_ae_restrict HL HM HT).
  - intro x; exact (Hf (oval_code e x)).
  - intro y; exact (Hg (oval_code d y)).
  - intros x y [Hxy [Hx Hy]]; apply Hfg.
    exists x, y; repeat split; try exact: oval_code_spec; exact Hxy.
Qed.

Theorem oval_coded_bidual {A B} (T : A -> B -> Prop)
    (L : OmegaVal R A) (M : OmegaVal R B) e d :
  oval_ae L (oval_enumerated e) -> oval_ae M (oval_enumerated d) ->
  oval_bidual T L M ->
  oval_bidual (oval_code_relation e d T) (oval_coded L e) (oval_coded M d).
Proof.
  intros HL HM [HT HT']; split; first exact (oval_coded_dual HL HM HT).
  intros f g Hf Hg Hfg; apply (oval_coded_dual HM HL HT'); auto.
  intros j i [y [x [Hy [Hx Hxy]]]]; apply Hfg; exists x, y; auto.
Qed.

Definition oval_pair_decode {A B} (e : nat -> option A)
    (d : nat -> option B) (ij : nat * nat) : OmegaVal R (A * B) :=
  match e (fst ij), d (snd ij) with
  | Some x, Some y => oval_ret R (x,y)
  | _, _ => oval_bottom R
  end.

(** Invalid codes contribute bottom, but cannot lose mass: concentration of
    the input joint on code_relation ensures both codes are valid almost surely.
    Enumerations may have duplicates and neither carrier need be inhabited. *)
Theorem oval_joint_decode {A B} (T : A -> B -> Prop)
    (L : OmegaVal R A) (M : OmegaVal R B) e d N K J :
  oval_eq L (oval_bind N (oval_decode R e)) ->
  oval_eq M (oval_bind K (oval_decode R d)) ->
  oval_joint (oval_code_relation e d T) N K J ->
  oval_joint T L M (oval_bind J (oval_pair_decode e d)).
Proof.
  intros HL HM [HJl [HJr HJS]]; split.
  - intros f Hf; rewrite (HL f Hf).
    transitivity (oval_eval J (fun ij => oval_eval (oval_decode R e (fst ij)) f)).
    + apply HJS.
      * intro ij; exact (oval_eval_bounds (oval_pair_decode e d ij) (fun z => Hf (fst z))).
      * intro ij; exact (oval_eval_bounds (oval_decode R e (fst ij)) Hf).
      * intros [i j] [x [y [Hx [Hy Hxy]]]].
        change (oval_eval (oval_pair_decode e d (i,j)) (fun z => f (fst z)) =
          oval_eval (oval_decode R e i) f).
        by rewrite /oval_pair_decode /oval_decode /= Hx Hy.
    + exact (HJl (fun i => oval_eval (oval_decode R e i) f)
        (fun i => oval_eval_bounds (oval_decode R e i) Hf)).
  - split.
    + intros g Hg; rewrite (HM g Hg).
      transitivity (oval_eval J (fun ij => oval_eval (oval_decode R d (snd ij)) g)).
      * apply HJS.
        -- intro ij; exact (oval_eval_bounds (oval_pair_decode e d ij) (fun z => Hg (snd z))).
        -- intro ij; exact (oval_eval_bounds (oval_decode R d (snd ij)) Hg).
        -- intros [i j] [x [y [Hx [Hy Hxy]]]].
           change (oval_eval (oval_pair_decode e d (i,j)) (fun z => g (snd z)) =
             oval_eval (oval_decode R d j) g).
           by rewrite /oval_pair_decode /oval_decode /= Hx Hy.
      * exact (HJr (fun j => oval_eval (oval_decode R d j) g)
          (fun j => oval_eval_bounds (oval_decode R d j) Hg)).
    + intros f g Hf Hg Hfg; apply HJS.
      * intro ij; exact (oval_eval_bounds (oval_pair_decode e d ij) Hf).
      * intro ij; exact (oval_eval_bounds (oval_pair_decode e d ij) Hg).
      * intros [i j] [x [y [Hx [Hy Hxy]]]].
        change (oval_eval (oval_pair_decode e d (i,j)) f = oval_eval (oval_pair_decode e d (i,j)) g).
        rewrite /oval_pair_decode /= Hx Hy; apply Hfg; exact Hxy.
Qed.

(** A proved reduction, NOT a transport-existence premise: construct the
    coded marginals and constraints, and return an explicit decoder for any
    actual coded joint. Nothing here supplies such a joint. *)
Theorem oval_countable_transport_reduction {A B} (T : A -> B -> Prop)
    (L : OmegaVal R A) (M : OmegaVal R B) :
  oval_countably_supported L -> oval_countably_supported M -> oval_bidual T L M ->
  exists e d (N K : OmegaVal R nat),
    oval_mass N = oval_mass L /\ oval_mass K = oval_mass M /\
    oval_bidual (oval_code_relation e d T) N K /\
    (forall J, oval_joint (oval_code_relation e d T) N K J ->
      oval_joint T L M (oval_bind J (oval_pair_decode e d))).
Proof.
  intros [e HL] [d HM] HT; exists e, d, (oval_coded L e), (oval_coded M d).
  split; first reflexivity.
  split; first reflexivity.
  split; first exact (oval_coded_bidual HL HM HT).
  intros J HJ; exact (oval_joint_decode (oval_coded_representation HL)
    (oval_coded_representation HM) HJ).
Qed.
End Transport.
