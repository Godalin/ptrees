(** Eventful behavioral iteration through the generic handler machine.
    The protocol is proof infrastructure, not a replacement for PTree.iter.
    Its configurations retain active-step continuations as well as entries
    and exits. No termination, no-event or candidate-closure premise is used.
    This owner depends on Interp adequacy; Eq must not import it backwards. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Program Require Import Equality.
From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder RelationalClosure.
From PTree.Eq Require Import PStruct Shallow PEutt Relation.
From PTree.Eq Require Import PrimitiveStableHitting PTreeKernel UnifiedFrontier
  RelationalHitting StableHittingRelation.
From PTree.Interp Require Import HandlerMachine HandlerMachineAcceleration.
Set Implicit Arguments.
Unset Strict Implicit.
Local Notation "` R" := (elem R) (at level 10).

Variant iterationE (I A : Type) : Type -> Type :=
| IterateStep : I -> iterationE I A (I+A).
Arguments IterateStep {I A} _.

CoFixpoint iteration_protocol {I A MN} (i : I) : ptree (iterationE I A) MN A :=
  Vis (IterateStep i) (fun r => match r with
    | inl j => iteration_protocol j | inr a => Ret a end).

Definition iteration_handler {I A E MN} (step : I -> ptree E MN (I+A))
    X (e : iterationE I A X) : ptree E MN X :=
  match e with IterateStep i => step i end.

Section Structural.
Context {E MN : Type -> Type} {I A : Type} (step : I -> ptree E MN (I+A)).
Definition iteration_left (r : I+A) :=
  PTree.interp (iteration_handler step)
    (match r with inl j => iteration_protocol j | inr a => Ret a end).
Definition iteration_right (r : I+A) :=
  match r with inl j => Tau (PTree.iter step j) | inr a => Ret a end.
Definition iteration_structural_candidate (t u : ptree E MN A) : Prop :=
  (exists i, observe t = observe (PTree.interp (iteration_handler step) (iteration_protocol i)) /\
    observe u = observe (Tau (PTree.iter step i))) \/
  (exists active : ptree E MN (I+A),
    observe t = observe (PTree.bind active iteration_left) /\
    observe u = observe (PTree.bind active iteration_right)).

(** Interp guards before a step; iter guards after a retry. A single
    leading Tau aligns the two schedules, including nonreturning steps. *)
Theorem iteration_protocol_iter i :
  pstruct eq (PTree.interp (iteration_handler step) (iteration_protocol i)) (Tau (PTree.iter step i)).
Proof.
  assert (H : forall t u, iteration_structural_candidate t u -> pstruct eq t u).
  { unfold pstruct. coinduction CH CIH. intros t u Htu. unfold pstruct_body.
    change (pstructF eq (` CH) (observe t) (observe u)).
    destruct Htu as [[j [Ht Hu]]|[active [Ht Hu]]]; rewrite Ht, Hu.
    - change (pstructF eq (` CH)
        (TauF (PTree.bind (step j) iteration_left)) (TauF (PTree.iter step j))).
      constructor. apply CIH. right. exists (step j). split; reflexivity.
    - change (pstructF eq (` CH) (observe (PTree.bind active iteration_left))
        (observe (PTree.bind active iteration_right))).
      rewrite !observe_bind. destruct (observe active) as [[j|a]|v|X e k|X mu k]; cbn.
      + change (pstructF eq (` CH)
          (TauF (PTree.bind (step j) iteration_left)) (TauF (PTree.iter step j))).
        constructor. apply CIH. right. exists (step j). split; reflexivity.
      + constructor. reflexivity.
      + constructor. apply CIH. right. exists v. split; reflexivity.
      + constructor. intro x. apply CIH. right. exists (k x). split; reflexivity.
      + constructor. intro x. apply CIH. right. exists (k x). split; reflexivity. }
  apply H. left. exists i. split; reflexivity.
Qed.
End Structural.

Section HeterogeneousMachine.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{BindOrd : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MixedOrd : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variables (Hzero : relational_zero FO) (Hlimit : relational_lub FO).
Context {I1 I2 A B : Type}.
Variables (step1 : I1 -> ptree E MN (I1+A)) (step2 : I2 -> ptree E MN (I2+B)).
Variables (SI : I1 -> I2 -> Prop) (RR : A -> B -> Prop).
Local Notation SR := (pstruct_iter_sum_rel SI RR).
Hypothesis Hstep : forall i j, SI i j -> peutt (MF := MF) SR (step1 i) (step2 j).
Local Notation h1 := (iteration_handler step1).
Local Notation h2 := (iteration_handler step2).
Local Notation C1 := (@handler_config (iterationE I1 A) E MN A).
Local Notation C2 := (@handler_config (iterationE I2 B) E MN B).
Local Definition next1 (r : I1+A) : ptree (iterationE I1 A) MN A :=
  match r with inl i => iteration_protocol i | inr a => Ret a end.
Local Definition next2 (r : I2+B) : ptree (iterationE I2 B) MN B :=
  match r with inl i => iteration_protocol i | inr b => Ret b end.

(** Unlike the entry-only candidate, active configurations retain arbitrary
    related residual steps after visible interaction. Return to an entry is
    an internal transition, never an unguarded coinductive hypothesis. *)
Inductive iteration_configs : C1 -> C2 -> Prop :=
| IterationEntry i j : SI i j -> iteration_configs (SourceConfig (iteration_protocol i)) (SourceConfig (iteration_protocol j))
| IterationExit a b : RR a b -> iteration_configs (SourceConfig (Ret a)) (SourceConfig (Ret b))
| IterationActive t u : peutt (MF := MF) SR t u ->
    iteration_configs (HandlerConfig t next1) (HandlerConfig u next2).

Definition iteration_states (s : ptree' E MN A) (v : ptree' E MN B) : Prop :=
  exists c d, s = observe (handler_config_tree h1 c) /\
    v = observe (handler_config_tree h2 d) /\ iteration_configs c d.
Local Notation HR := (@ptree_stable_head_rel E MN A B RR iteration_states).

Local Lemma chosen_head_lift {G1 G2 X Y} (t : ptree G1 MN X) (u : ptree G2 MN Y)
    a b (R : stable_head G1 MN X -> stable_head G2 MN Y -> Prop) :
  ptree_stable_hitting (MF := MF) (observe t) (sem_ret a) ->
  ptree_stable_hitting (MF := MF) (observe u) (sem_ret b) -> R a b ->
  sem_lift R (handler_complete_front t) (handler_complete_front u).
Proof.
  intros Ht Hu Hab.
  eapply sem_lift_proper_l.
  - eapply stable_hitting_unique; [exact Ht|apply handler_complete_front_hitting].
  - eapply sem_lift_proper_r.
    + eapply stable_hitting_unique; [exact Hu|apply handler_complete_front_hitting].
    + apply sem_lift_ret. exact Hab.
Qed.

Lemma iteration_kernel_related c d : iteration_configs c d ->
  sem_lift (stable_target_rel iteration_configs HR)
    (handler_machine_kernel h1 c) (handler_machine_kernel h2 d).
Proof.
  intro H. destruct H as [i j Hij|a b Hab|t u Htu]; unfold handler_machine_kernel.
  - eapply sem_lift_bind with (R := fun a b =>
      a = FHVis (IterateStep i) next1 /\ b = FHVis (IterateStep j) next2).
    + eapply chosen_head_lift.
      * apply stable_hitting_vis.
      * apply stable_hitting_vis.
      * split; reflexivity.
    + intros a b [-> ->]. apply sem_lift_ret.
      change (iteration_configs (HandlerConfig (step1 i) next1) (HandlerConfig (step2 j) next2)).
      constructor. apply Hstep. exact Hij.
  - eapply sem_lift_bind with (R := fun h j => h = FHRet a /\ j = FHRet b).
    + eapply chosen_head_lift; [apply stable_hitting_ret|apply stable_hitting_ret|split; reflexivity].
    + intros h j [-> ->]. apply sem_lift_ret. constructor. exact Hab.
  - eapply sem_lift_bind.
    + eapply peutt_hitting_lift;
        [exact Htu|apply handler_complete_front_hitting|apply handler_complete_front_hitting].
    + intros a b Hab. apply sem_lift_ret. dependent destruction Hab.
      * destruct H.
        -- apply IterationEntry. assumption.
        -- apply IterationExit. assumption.
      * constructor. intro x.
        exists (HandlerConfig (k1 x) next1), (HandlerConfig (k2 x) next2).
        split; [reflexivity|split; [reflexivity|]]. constructor. apply H.
Qed.

(** Couple complete machine executions, then reuse adequacy independently
    for the two different protocol effect signatures. *)
Theorem iteration_machine_related c d : iteration_configs c d ->
  peutt (MF := MF) RR (handler_config_tree h1 c) (handler_config_tree h2 d).
Proof.
  intro H. eapply peutt_coinduction with (sim := iteration_states).
  - intros s v [c' [d' [-> [-> Hcd]]]].
    destruct (stable_hitting_exists (handler_machine_kernel h1) c') as [mu Hmu].
    destruct (stable_hitting_exists (handler_machine_kernel h2) d') as [nu Hnu].
    eapply stable_hitting_match_of_hitting_lift.
    + exact (handler_machine_hitting_sound (Directed := Directed) Hmu).
    + exact (handler_machine_hitting_sound (Directed := Directed) Hnu).
    + eapply (stable_hitting_rel (relational_bind_of_laws FB) Hzero iteration_kernel_related Hlimit);
        eassumption.
  - exists c, d. split; [reflexivity|split; [reflexivity|exact H]].
Qed.

Corollary iteration_protocol_related i j : SI i j ->
  peutt (MF := MF) RR (PTree.interp h1 (iteration_protocol i)) (PTree.interp h2 (iteration_protocol j)).
Proof. intro Hij. apply (iteration_machine_related (c := SourceConfig _) (d := SourceConfig _)).
  constructor. exact Hij. Qed.
End HeterogeneousMachine.

Section Compose.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}.
Local Lemma iteration_peutt_compose {A B C}
    (R12 : A -> B -> Prop) (R23 : B -> C -> Prop) (R13 : A -> C -> Prop)
    (Hret : forall a b c, R12 a b -> R23 b c -> R13 a c)
    (t : ptree E MN A) (u : ptree E MN B) (v : ptree E MN C) :
  peutt (MF := MF) R12 t u -> peutt (MF := MF) R23 u v -> peutt (MF := MF) R13 t v.
Proof.
  intros H12 H23. unfold peutt, peutt_state in H12, H23 |- *.
  eapply stable_hitting_bisim_compose; [|exact H12|exact H23].
  intros sim12 sim23 sim13 Hsim a1 a3 [a2 [Ha12 Ha23]].
  dependent destruction Ha12; dependent destruction Ha23.
  - constructor. eapply Hret; eassumption.
  - constructor. intro x. apply Hsim. eauto.
Qed.
End Compose.

Section Final.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{BindOrd : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MixedOrd : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variables (Hmixed : relational_mixed_bind NI FI MX)
  (Hzero : relational_zero FO) (Hlimit : relational_lub FO).
Local Notation structural :=
  (Relation.peutt_of_pstruct (relational_bind_of_laws FB) Hmixed Hzero Hlimit).

(** Public relational congruence. The state relation and return relation
    are arbitrary and may have different carriers on the two sides. *)
Theorem peutt_iter_eventful_rel {I1 I2 A B}
    (step1 : I1 -> ptree E MN (I1+A)) (step2 : I2 -> ptree E MN (I2+B))
    (SI : I1 -> I2 -> Prop) (RR : A -> B -> Prop)
    (Hstep : forall i j, SI i j ->
      peutt (MF := MF) (pstruct_iter_sum_rel SI RR) (step1 i) (step2 j)) i j :
  SI i j -> peutt (MF := MF) RR (PTree.iter step1 i) (PTree.iter step2 j).
Proof.
  intro Hij.
  assert (HL : peutt (MF := MF) eq (PTree.iter step1 i)
      (PTree.interp (iteration_handler step1) (iteration_protocol i))).
  { eapply peutt_trans; [apply peutt_tau_r|].
    apply peutt_sym. apply structural. apply iteration_protocol_iter. }
  assert (HR : peutt (MF := MF) eq (PTree.interp (iteration_handler step2) (iteration_protocol j))
      (PTree.iter step2 j)).
  { eapply peutt_trans; [apply structural; apply iteration_protocol_iter|apply peutt_tau_l]. }
  eapply (iteration_peutt_compose (R12 := eq) (R23 := RR) (R13 := RR)).
  - intros a b c -> H. exact H.
  - exact HL.
  - eapply (iteration_peutt_compose (R12 := RR) (R23 := eq) (R13 := RR)).
    + intros a b c H <-. exact H.
    + exact (iteration_protocol_related Hzero Hlimit Hstep Hij).
    + exact HR.
Qed.
(** Homogeneous client; relation inference remains explicit in the relational
    theorem. No global rewriting instance is registered. *)
Corollary peutt_iter_eventful {I A}
    (step1 step2 : I -> ptree E MN (I+A))
    (Hstep : forall i, peutt (MF := MF) eq (step1 i) (step2 i)) i :
  peutt (MF := MF) eq (PTree.iter step1 i) (PTree.iter step2 i).
Proof.
  eapply peutt_iter_eventful_rel with (SI := eq); [|reflexivity].
  intros x y ->. eapply peutt_rel_mono; [|apply Hstep].
  intros r s ->. destruct s; constructor; reflexivity.
Qed.

End Final.
