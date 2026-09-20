(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From Coq.Classes Require Import RelationClasses.
From Coq.Logic Require Import ClassicalDescription.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.Backend Require Import TwoLevelMeasureSubEnum FrontierLiftEnum.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure FreeOmegaNative.
From PTree.Prob.Backend.FreeOmega Require Import FreeOmegaRecoverySubEnum FreeOmegaCodedJointSubEnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A finite Boolean signature codes equivalence classes on the relevant
    support.  The probes may be higher-universe trees; the label list bool
    stays small.  No quotient type or measurable structure on trees is used. *)
Definition finite_equivalence_code {A} (R : A -> A -> Prop) (probes : list A) a :=
  List.map (fun probe => if excluded_middle_informative (R probe a) then true else false) probes.

Lemma finite_equivalence_code_respects {A} (R : A -> A -> Prop)
    (ER : Equivalence R) probes a b :
  R a b -> finite_equivalence_code R probes a = finite_equivalence_code R probes b.
Proof.
  destruct ER as [Hrefl Hsym Htrans]. intro Hab.
  induction probes as [|probe probes IH]; [reflexivity|].
  cbn [finite_equivalence_code List.map]. f_equal; [|exact IH].
  destruct (excluded_middle_informative (R probe a)) as [Ha|Ha];
    destruct (excluded_middle_informative (R probe b)) as [Hb|Hb]; try reflexivity.
  - exfalso. apply Hb. exact (Htrans _ _ _ Ha Hab).
  - exfalso. apply Ha. exact (Htrans _ _ _ Hb (Hsym _ _ Hab)).
Qed.

Lemma finite_equivalence_code_separates {A} (R : A -> A -> Prop)
    (Hrefl : Reflexive R) probes a b :
  List.In a probes ->
  finite_equivalence_code R probes a = finite_equivalence_code R probes b -> R a b.
Proof.
  induction probes as [|probe probes IH]; [contradiction|].
  intros [<-|Hin] Hcode.
  - cbn [finite_equivalence_code List.map] in Hcode.
    destruct (excluded_middle_informative (R probe probe)) as [Hpp|Hpp];
      [|exfalso; apply Hpp; apply Hrefl].
    destruct (excluded_middle_informative (R probe b)); [assumption|discriminate].
  - apply IH; [exact Hin|]. injection Hcode as Hhead Htail. exact Htail.
Qed.

Section EquivalenceJoint.
Context {A : Type} (R : A -> A -> Prop) (ER : Equivalence R).
Variable p q : free_omega_native_presentation SubEnum A.
Let X := native_sample_type p.
Let Y := native_sample_type q.
Let mu := native_sample_measure p.
Let nu := native_sample_measure q.
Let probes := List.map (fun wx => native_sample_value p (snd wx)) (subenum_raw mu).
Let code := finite_equivalence_code R probes.
Let lc := fun x => code (native_sample_value p x).
Let rc := fun y => code (native_sample_value q y).

Lemma equivalence_probes_support : sem_ae mu (fun x => List.In (native_sample_value p x) probes).
Proof.
  intros weight x Hin _. unfold probes. apply List.in_map_iff.
  exists (weight,x). split; [reflexivity|exact Hin].
Qed.

(** Genuine extraction from a quotient coupling, under an explicit
    EQUIVALENCE hypothesis.  This does not assert realization for arbitrary
    relations; equivalence remains an explicit hypothesis of this lemma. *)
Theorem subenum_equivalence_quotient_joint :
  free_omega_qlift R (free_omega_native p) (free_omega_native q) ->
  exists (Z : Type) (joint : SubEnum Z)
    (left : Z -> X) (right : Z -> Y),
    free_omega_qlift (fun z x => left z = x)
      (FOSample joint (fun z => FORet z) : FreeOmegaAt SubEnum A Z)
      (FOSample mu (fun x => FORet x)) /\
    free_omega_qlift (fun z y => right z = y)
      (FOSample joint (fun z => FORet z) : FreeOmegaAt SubEnum A Z)
      (FOSample nu (fun y => FORet y)) /\
    sem_ae joint (fun z => R (native_sample_value p (left z)) (native_sample_value q (right z))).
Proof.
  intro Hdecoded.
  pose proof (subenum_native_coupling_pullback Hdecoded) as Hpaths.
  assert (Hcodes : free_omega_qlift (fun x y => lc x = rc y)
    (FOSample mu (fun x => FORet x) : FreeOmegaAt SubEnum A X)
    (FOSample nu (fun y => FORet y) : FreeOmegaAt SubEnum A Y)).
  { eapply FOQLMono; [exact Hpaths|]. intros x y Hxy.
    exact (@finite_equivalence_code_respects A R ER probes
      (native_sample_value p x) (native_sample_value q y) Hxy). }
  destruct (subenum_coded_quotient_joint (Anchor := A) Hcodes) as [joint [Hl [Hr Hcode]]].
  exists _, joint, (@projT1 X (fun _ => (list bool * Y)%type)),
    (fun z : {x : X & (list bool * Y)%type} => snd (projT2 z)).
  split; [exact Hl|]. split; [exact Hr|].
  assert (Hprobes : sem_ae joint (fun z => List.In (native_sample_value p (projT1 z)) probes)).
  { assert (Hae : free_omega_ae (fun x => List.In (native_sample_value p x) probes)
      (FOSample mu (fun x => FORet x) : FreeOmegaAt SubEnum A X)).
    { apply FOAESample with (Good := fun x => List.In (native_sample_value p x) probes);
        [apply equivalence_probes_support|]. intros x Hx. apply FOAERet. exact Hx. }
    pose proof (proj2 (free_omega_qlift_support Hl) _ Hae) as Htransport.
    apply free_omega_ae_sample_inv in Htransport.
    eapply sem_ae_mono; [|exact Htransport]. intros z Hz.
    assert (Himage : exists x, projT1 z = x /\ List.In (native_sample_value p x) probes)
      by (inversion Hz; assumption).
    destruct Himage as [x [<- Hx]]. exact Hx. }
  eapply sem_ae_mono with (P := fun z =>
    List.In (native_sample_value p (projT1 z)) probes /\ lc (projT1 z) = rc (snd (projT2 z))).
  - intros z [Hz Hlabels]. eapply finite_equivalence_code_separates.
    + exact (@Equivalence_Reflexive A R ER).
    + exact Hz.
    + exact Hlabels.
  - apply sem_ae_conj; assumption.
Qed.
End EquivalenceJoint.
