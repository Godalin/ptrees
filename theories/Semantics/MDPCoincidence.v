(** Role: Comparison semantics. Depends on canonical theory; not the canonical peutt relation or interpreter theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Program Require Import Equality.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.
From PTree.Semantics Require Import HeadTransition MDPFragment TreeTransition TreeTransitionBisim TreeTransitionSoundness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Separation is explicit and uses an EXISTING capability: exact AE at
    Dirac measures. No equality-coupling reflection is assumed. *)
Section Coincidence.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}
  `{FCAE : @SemanticMeasureCouplingAELaws MF FI}
  `{FOAE : @SemanticOmegaAELaws MF FI FO}
  `{FD : @SemanticMeasureDiracAELaws MF FI}.
Context {R : Type}.
Local Notation tree := (ptree E MN R).
Local Notation head := (stable_head E MN R).
Local Notation K := (@ptree_primitive_kernel E MN MF FI MX R).
Local Notation hits t out := (stable_hitting K (observe t) out).
Local Notation TB := (@tree_trans_bisim E MN MF FI FC MX FO R R eq).
Local Notation good := (@mdp_head E MN MF FI FC MX FO R).
Local Notation state := (@mdp_state E MN MF FI FC MX FO R).

Lemma mdp_lift_dirac_inv {A B} (rel : A -> B -> Prop) a b :
  sem_lift rel (sem_ret a) (sem_ret b) -> rel a b.
Proof.
  intro Hlift.
  assert (Ha : sem_ae (sem_ret a) (fun x => x = a)).
  { apply (proj2 (sem_ae_ret_iff _ _)). reflexivity. }
  pose proof (sem_lift_ae_transport_r Hlift Ha) as Hb.
  apply (proj1 (sem_ae_ret_iff _ _)) in Hb.
  destruct Hb as [x [Hrel ->]]. exact Hrel.
Qed.

Lemma mdp_ret_zero_separate {A} (a : A) :
  ~ sem_lift eq (sem_ret a) sem_zero.
Proof.
  intro H. pose proof (sem_lift_sym H) as Hback.
  pose proof (sem_lift_ae_transport_r Hback (sem_ae_zero (fun _ : A => False))) as Ha.
  apply (proj1 (sem_ae_ret_iff _ _)) in Ha.
  destruct Ha as [b [_ Hfalse]]. contradiction.
Qed.

(** Transport across equality couplings, NOT sem_eq reflection. *)
Lemma mdp_lift_transport {A B} (rel : A -> B -> Prop) a a' b b' :
  sem_lift eq a a' -> sem_lift eq b b' -> sem_lift rel a b -> sem_lift rel a' b'.
Proof.
  intros Ha Hb Hab.
  assert (Ha' : sem_lift eq a' a).
  { eapply sem_lift_mono; [|apply sem_lift_sym; exact Ha]. intros x y H. symmetry. exact H. }
  assert (Hab' : sem_lift rel a' b).
  { eapply sem_lift_mono; [|eapply sem_lift_comp; [exact Ha'|exact Hab]].
    intros x y [z [-> Hz]]. exact Hz. }
  eapply sem_lift_mono; [|eapply sem_lift_comp; [exact Hab'|exact Hb]].
  intros x y [z [Hx ->]]. exact Hx.
Qed.

Lemma mdp_dirac_bind_lift {A B} (front : MF A) h (project : A -> MF B) :
  sem_eq front (sem_ret h) -> sem_lift eq (sem_bind front project) (project h).
Proof.
  intro Heq.
  eapply sem_lift_proper_r; [exact (sem_bind_ret_l h project)|].
  eapply sem_lift_bind with (R := eq).
  - eapply sem_lift_proper_r; [exact Heq|]. apply sem_lift_refl. intro x. reflexivity.
  - intros x y ->. apply sem_lift_refl. intro z. reflexivity.
Qed.

Lemma mdp_dirac_observations {O} (project : head -> MF O) t front h :
  hits t front -> sem_eq front (sem_ret h) ->
  tree_head_observation project t (sem_bind front project) /\
  sem_lift eq (sem_bind front project) (project h).
Proof.
  intros Hhit Heq. split.
  - exists front. split; [exact Hhit|apply sem_eq_refl].
  - apply mdp_dirac_bind_lift. exact Heq.
Qed.

Lemma mdp_dirac_transition t front h label out :
  hits t front -> sem_eq front (sem_ret h) -> head_action_result label h out ->
  tree_trans t label (sem_bind front (fun _ : head => out)) /\
  sem_lift eq (sem_bind front (fun _ : head => out)) out.
Proof.
  intros Hhit Heq Haction. split.
  - apply tree_trans_from_hitting; [exact Hhit|].
    assert (Hlift : sem_lift eq (sem_ret h) front).
    { eapply sem_lift_proper_r; [apply sem_eq_sym; exact Heq|].
      apply sem_lift_refl. intro x. reflexivity. }
    assert (Hae : sem_ae (sem_ret h) (fun k => head_action_result label k out)).
    { apply (proj2 (sem_ae_ret_iff _ _)). exact Haction. }
    pose proof (sem_lift_ae_transport_r Hlift Hae) as Hfront.
    eapply sem_ae_mono; [|exact Hfront]. intros k [k' [-> Hk]]. exact Hk.
  - exact (mdp_dirac_bind_lift (fun _ : head => out) Heq).
Qed.

Lemma mdp_dirac_return_match t u f g h k :
  TB t u -> hits t f -> sem_eq f (sem_ret h) -> hits u g -> sem_eq g (sem_ret k) ->
  sem_lift eq (return_projection (MF := MF) h) (return_projection (MF := MF) k).
Proof.
  intros Htb Hf Hh Hg Hk.
  destruct (mdp_dirac_observations return_projection Hf Hh) as [Hobs1 Hlift1].
  destruct (mdp_dirac_observations return_projection Hg Hk) as [Hobs2 Hlift2].
  eapply mdp_lift_transport; [exact Hlift1|exact Hlift2|].
  exact (tree_trans_bisim_return_observations Htb Hobs1 Hobs2).
Qed.

Lemma mdp_dirac_event_match t u f g h k :
  TB t u -> hits t f -> sem_eq f (sem_ret h) -> hits u g -> sem_eq g (sem_ret k) ->
  sem_lift eq (offered_event_projection (MF := MF) h) (offered_event_projection (MF := MF) k).
Proof.
  intros Htb Hf Hh Hg Hk.
  destruct (mdp_dirac_observations offered_event_projection Hf Hh) as [Hobs1 Hlift1].
  destruct (mdp_dirac_observations offered_event_projection Hg Hk) as [Hobs2 Hlift2].
  eapply mdp_lift_transport; [exact Hlift1|exact Hlift2|].
  exact (tree_trans_bisim_offered_observations Htb Hobs1 Hobs2).
Qed.

Lemma mdp_dirac_successor_match t u f g h k label out1 out2 :
  TB t u -> hits t f -> sem_eq f (sem_ret h) -> hits u g -> sem_eq g (sem_ret k) ->
  head_step h label out1 -> head_step k label out2 ->
  sem_lift (tree_trans_head_rel TB) out1 out2.
Proof.
  intros Htb Hf Hh Hg Hk Hstep1 Hstep2.
  destruct (mdp_dirac_transition Hf Hh (HARMatch Hstep1)) as [Ht1 Hl1].
  destruct (mdp_dirac_transition Hg Hk (HARMatch Hstep2)) as [Ht2 Hl2].
  eapply mdp_lift_transport; [exact Hl1|exact Hl2|].
  exact (tree_trans_bisim_transitions Htb Ht1 Ht2).
Qed.

Lemma stable_head_tree_hitting h : hits (stable_head_tree h) (sem_ret h).
Proof.
  destruct h as [r|X e k]; [apply ptree_stable_hitting_ret|apply ptree_stable_hitting_vis].
Qed.

(** Proof-local head relation retains arbitrary raw representatives. This
    avoids assuming their chosen Dirac measures are literal hitting
    witnesses, or that sem_lift eq reflects sem_eq. *)
Inductive fragment_head_pair (h k : head) : Prop :=
  | FragmentHeads (t u : tree) f g :
      good h -> good k -> hits t f -> sem_eq f (sem_ret h) ->
      hits u g -> sem_eq g (sem_ret k) -> TB t u -> fragment_head_pair h k.

Local Definition fragment_distribution_pair (s1 s2 : ptree' E MN R) : Prop :=
  exists f g, stable_hitting K s1 f /\ stable_hitting K s2 g /\
    sem_lift fragment_head_pair f g.

Local Lemma fragment_head_pair_of_stable h k :
  good h -> good k -> tree_trans_head_rel TB h k -> fragment_head_pair h k.
Proof.
  intros Hh Hk Htb. econstructor; [exact Hh|exact Hk| | | | |exact Htb].
  - apply stable_head_tree_hitting.
  - apply sem_eq_refl.
  - apply stable_head_tree_hitting.
  - apply sem_eq_refl.
Qed.

Local Lemma fragment_head_pair_progress h k : fragment_head_pair h k ->
  ptree_stable_head_rel eq fragment_distribution_pair h k.
Proof.
  intros [t u f g Hgood1 Hgood2 Hf Hh Hg Hk Htb].
  pose proof (mdp_dirac_return_match Htb Hf Hh Hg Hk) as Hret.
  pose proof (mdp_dirac_event_match Htb Hf Hh Hg Hk) as Hevent.
  destruct h as [r|X e cont1], k as [s|Y event cont2]; cbn in Hret, Hevent.
  - constructor. exact (mdp_lift_dirac_inv Hret).
  - exfalso. exact (mdp_ret_zero_separate Hret).
  - exfalso. apply (mdp_ret_zero_separate (a := s)).
    eapply sem_lift_mono; [|apply sem_lift_sym; exact Hret]. intros a b ->. reflexivity.
  - apply mdp_lift_dirac_inv in Hevent. dependent destruction Hevent.
    constructor. intro x.
    destruct (proj1 (mdp_head_vis_iff event cont1) Hgood1 x) as [out1 [Hhit1 [Ht1 Ha1]]].
    destruct (proj1 (mdp_head_vis_iff event cont2) Hgood2 x) as [out2 [Hhit2 [Ht2 Ha2]]].
    exists out1, out2. split; [exact Hhit1|]. split; [exact Hhit2|].
    assert (Hstep1 : head_step (FHVis event cont1) (Obs event x) out1) by (constructor; exact Hhit1).
    assert (Hstep2 : head_step (FHVis event cont2) (Obs event x) out2) by (constructor; exact Hhit2).
    pose proof (mdp_dirac_successor_match Htb Hf Hh Hg Hk Hstep1 Hstep2) as Hcouple.
    pose proof (sem_lift_ae_restrict Hcouple Ha1 Ha2) as Hclosed.
    eapply sem_lift_mono; [|exact Hclosed]. intros a b [Hab [Ha Hb]].
    exact (fragment_head_pair_of_stable Ha Hb Hab).
Qed.

Local Lemma fragment_distribution_pair_peutt t u :
  fragment_distribution_pair (observe t) (observe u) -> peutt eq t u.
Proof.
  apply peutt_coinduction with (sim := fragment_distribution_pair).
  intros s1 s2 [f [g [Hf [Hg Hlift]]]].
  eapply stable_hitting_match_of_hitting_lift; [exact Hf|exact Hg|].
  eapply sem_lift_mono; [apply fragment_head_pair_progress|exact Hlift].
Qed.

Theorem mdp_state_tree_trans_bisim_peutt (t u : tree) :
  state t -> state u -> TB t u -> peutt eq t u.
Proof.
  intros [h [f [Hf [Hh Hgood1]]]] [k [g [Hg [Hk Hgood2]]]] Htb.
  apply fragment_distribution_pair_peutt.
  exists f, g. split; [exact Hf|]. split; [exact Hg|].
  eapply sem_lift_proper_l; [apply sem_eq_sym; exact Hh|].
  eapply sem_lift_proper_r; [apply sem_eq_sym; exact Hk|].
  apply sem_lift_ret. eapply FragmentHeads with (t := t) (u := u) (f := f) (g := g);
    eassumption.
Qed.

Theorem mdp_state_peutt_tree_trans_iff
    `{FOrd : @SemanticMeasureOrderLaws MF FI FO} (t u : tree) :
  state t -> state u -> (peutt eq t u <-> TB t u).
Proof.
  intros Ht Hu. split.
  - intro H. exact (peutt_tree_trans_bisim (FI := FI) (FC := FC) (FO := FO)
      (FOrd := FOrd) H).
  - exact (mdp_state_tree_trans_bisim_peutt Ht Hu).
Qed.
End Coincidence.
