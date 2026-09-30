(** Native/frontier reflection and classical MDP correspondence. The
    reflection premise concerns only mapped probability measures, never
    trees or bisimulation. Models discharge it separately. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel PEutt StableHittingRelation.
From PTree.Semantics Require Import HeadTransition MDPFragment MDPEmbedding
  TreeTransitionBisim MDPCoincidence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Reflection.
Context {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}
  `{FCAE : @SemanticMeasureCouplingAELaws MF FI}
  `{FD : @SemanticMeasureDiracAELaws MF FI}.

(** Decoders need not be injective. This is a local probability obligation,
    not a new typeclass or a premise asserting the desired MDP theorem. *)
Hypothesis Hreflect : forall {X Y A B} (mu : MN X) (nu : MN Y)
    (f : X -> A) (g : Y -> B) (rel : A -> B -> Prop),
  sem_lift rel (mixed_bind mu (fun x => sem_ret (f x)))
    (mixed_bind nu (fun y => sem_ret (g y))) ->
  sem_lift (fun x y => rel (f x) (g y)) mu nu.

Section EncodedMDP.
Variable D : MDP MN.
Local Notation encode := (mdp_encode (D := D)).
Local Notation ehead := (mdp_encode_head (D := D)).
Local Notation E := (mdpE (mdp_observations D) (mdp_actions D)).
Local Notation hb := (@head_bisim E MN MF FI FC MX FO unit unit eq).
Local Notation pb := (@peutt E MN MF FI FC MX FO unit unit eq).

(** A literal transition iff additionally needs extensionality in the
    output of the limit relation, not just uniqueness of chosen limits. *)
Theorem mdp_encode_step_iff
    (Hlimit : forall A (c : nat -> MF A) mu nu,
      sem_eq mu nu -> sem_lub c mu -> sem_lub c nu) s a out :
  @head_step E MN MF FI MX FO unit
    (ehead s) (Obs (Choose (mdp_observe D s)) a) out <->
  sem_eq out (mdp_successors (D := D) (mdp_transition D s a)).
Proof.
  split; [apply (mdp_encode_step_unique (FI := FI) (FO := FO))|].
  intro Heq. constructor.
  eapply Hlimit; [apply sem_eq_sym; exact Heq|].
  apply (mdp_sample_hitting (FI := FI) (FO := FO) (MX := MX)).
Qed.

Theorem mdp_head_bisim_reflect s t : hb (ehead s) (ehead t) -> mdp_bisim (D := D) s t.
Proof.
  intro H. eapply mdp_bisim_coinduction with (sim := fun u v => hb (ehead u) (ehead v)).
  - intros u v Huv. apply head_bisim_unfold in Huv.
    apply mdp_choose_head_rel_iff in Huv. destruct Huv as [Hobs Hsteps].
    split; [exact Hobs|]. intro a.
    pose proof (stable_hitting_match_hitting_lift (Hsteps a)
      (mdp_sample_hitting (FI := FI) (FO := FO) (MX := MX) (D := D) (mdp_transition D u a))
      (mdp_sample_hitting (FI := FI) (FO := FO) (MX := MX) (D := D) (mdp_transition D v a))) as Hfront.
    exact (Hreflect Hfront).
  - exact H.
Qed.

Lemma mdp_encoded_vis_inversion s t : pb (encode s) (encode t) ->
  mdp_observe D s = mdp_observe D t /\
  forall a, pb (Prob (mdp_transition D s a) encode)
    (Prob (mdp_transition D t a) encode).
Proof.
  intro H.
  pose proof (peutt_hitting_lift H
    (mdp_encode_hitting (FI := FI) (FO := FO) (MX := MX) (D := D) s)
    (mdp_encode_hitting (FI := FI) (FO := FO) (MX := MX) (D := D) t)) as Hheads.
  apply sem_lift_ret_inv in Hheads.
  apply mdp_choose_head_rel_iff in Hheads. exact Hheads.
Qed.

Theorem mdp_peutt_reflect s t : pb (encode s) (encode t) -> mdp_bisim (D := D) s t.
Proof.
  intro H. eapply mdp_bisim_coinduction with (sim := fun u v => pb (encode u) (encode v)).
  - intros u v Huv. destruct (mdp_encoded_vis_inversion Huv) as [Hobs Hsteps].
    split; [exact Hobs|]. intro a.
    pose proof (peutt_hitting_lift (Hsteps a)
      (mdp_sample_hitting (FI := FI) (FO := FO) (MX := MX) (D := D) (mdp_transition D u a))
      (mdp_sample_hitting (FI := FI) (FO := FO) (MX := MX) (D := D) (mdp_transition D v a))) as Hfront.
    pose proof (Hreflect Hfront) as Hnative.
    eapply sem_lift_mono; [|exact Hnative].
    intros x y Hxy. eapply (peutt_of_hitting_lift (FI := FI) (FO := FO));
      [apply (mdp_encode_hitting (FI := FI) (FO := FO))|
       apply (mdp_encode_hitting (FI := FI) (FO := FO))|].
    apply sem_lift_ret. exact Hxy.
  - exact H.
Qed.

Theorem mdp_head_bisim_iff s t : mdp_bisim (D := D) s t <-> hb (ehead s) (ehead t).
Proof. split; [apply (mdp_bisim_head_sound (FI := FI) (FO := FO))|apply mdp_head_bisim_reflect]. Qed.

Theorem mdp_peutt_iff s t : mdp_bisim (D := D) s t <-> pb (encode s) (encode t).
Proof. split; [apply (mdp_bisim_peutt_sound (FI := FI) (FO := FO))|apply mdp_peutt_reflect]. Qed.

Context `{FOAE : @SemanticOmegaAELaws MF FI FO}.

(** The fragment-based correspondence is the public abstract boundary.
    Concrete backends may prove membership by any existing probability laws. *)
Theorem mdp_trans_bisim_iff_of_fragment
    (Hfragment : forall s, mdp_state (MF := MF) (encode s)) s t :
  mdp_bisim (D := D) s t <->
  @trans_bisim E MN MF FI FC MX FO unit unit eq (encode s) (encode t).
Proof.
  rewrite mdp_peutt_iff.
  apply mdp_state_peutt_trans_iff; apply Hfragment.
Qed.

Hypothesis Htotal : forall s a, sem_total (mdp_successors (D := D) (mdp_transition D s a)).
Hypothesis Hsupport : forall s a,
  sem_ae (mdp_successors (D := D) (mdp_transition D s a)) (fun h => exists t, h = ehead t).

Theorem mdp_trans_bisim_iff s t :
  mdp_bisim (D := D) s t <->
  @trans_bisim E MN MF FI FC MX FO unit unit eq (encode s) (encode t).
Proof.
  apply mdp_trans_bisim_iff_of_fragment.
  apply mdp_encode_mdp_state; assumption.
Qed.

End EncodedMDP.

(** Separate source representation from the native/frontier reflection
    above. The source can be non-omega-complete: only its total kernel rows
    and faithful lifting into MN are needed. *)
Section RepresentedSource.
Context {MS : Type -> Type}
  `{SI : SemanticMeasure MS} `{SC : @SemanticMeasureCoreLaws MS SI}
  `{SO : @SemanticOmega MS SI}.
Variable source : MDP MS.
Variable kernel : mdp_states source -> mdp_actions source -> MN (mdp_states source).
Hypothesis kernel_total : forall s a, sem_total (kernel s a).
Hypothesis kernel_lift : forall (rel : mdp_states source -> mdp_states source -> Prop) s t a,
  sem_lift rel (mdp_transition source s a) (mdp_transition source t a) <->
  sem_lift rel (kernel s a) (kernel t a).
Let represented := mdp_represent (D := source) kernel_total.
Local Notation encoded s := (mdp_encode (D := represented) s).

Theorem mdp_represent_peutt_iff s t :
  mdp_bisim (D := source) s t <-> peutt (MF := MF) eq (encoded s) (encoded t).
Proof.
  rewrite (mdp_represent_bisim_iff kernel_total kernel_lift).
  apply (mdp_peutt_iff (D := represented)).
Qed.

Context `{FOAE : @SemanticOmegaAELaws MF FI FO}.
Theorem mdp_represent_trans_bisim_iff
    (Hfragment : forall s, mdp_state (MF := MF) (encoded s)) s t :
  mdp_bisim (D := source) s t <->
  trans_bisim (MF := MF) eq (encoded s) (encoded t).
Proof.
  rewrite mdp_represent_peutt_iff.
  apply mdp_state_peutt_trans_iff; apply Hfragment.
Qed.
End RepresentedSource.
End Reflection.
