(** State-indexed complete-frontier machine. Get/Put change an internal
    configuration; only a remaining effect releases a visible target head. *)
Set Universe Polymorphism.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed RelationalClosure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel
  PEutt RelationalHitting.
From PTree.Interp Require Import State HandlerMachine.
Set Implicit Arguments.
Unset Strict Implicit.

Section StateConfigurations.
Context {S : Type} {E MN : Type -> Type}.
Definition state_config (A : Type) := (S * ptree (stateE S +' E) MN A)%type.

Definition state_head_result {A} s (h : stable_head (stateE S +' E) MN A) :
    stable_target (state_config A) (stable_head E MN (S * A)) :=
  match h with
  | FHRet a => SHStable (FHRet (s,a))
  | @FHVis _ _ _ X e k =>
      match e with
      | inl1 se => let '(s',x) := state_response se s in
          @SHInternal (state_config A) (stable_head E MN (S*A)) (s',k x)
      | inr1 fe => SHStable (FHVis fe (fun x => run_state (k x) s))
      end
  end.
End StateConfigurations.

Section StateKernel.
Context {S : Type} {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}.

Definition state_primitive_kernel {A} (c : @state_config S E MN A) :
    MF (stable_target (@state_config S E MN A) (stable_head E MN (S * A))) :=
  let '(s,t) := c in
  match observe t with
  | RetF a => sem_ret (SHStable (FHRet (s,a)))
  | TauF u => sem_ret (SHInternal (s,u))
  | @VisF _ _ _ _ X e k => sem_ret (state_head_result s (FHVis e k))
  | @ProbF _ _ _ _ X mu k => mixed_bind mu (fun x => sem_ret (SHInternal (s,k x)))
  end.

Context `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Definition state_machine_kernel {A} (c : @state_config S E MN A) :
    MF (stable_target (@state_config S E MN A) (stable_head E MN (S * A))) :=
  sem_bind (handler_complete_front (snd c)) (fun h => sem_ret (state_head_result (fst c) h)).
End StateKernel.

Section StateSimulation.
Context {S : Type} {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variable Hbind : relational_bind FI.
Context {A B : Type} (RR : A -> B -> Prop).
Local Notation source_rel := (@peutt (stateE S +' E) MN MF FI FC MX FO A B RR).

Definition state_config_rel (c : @state_config S E MN A) (d : @state_config S E MN B) :=
  fst c = fst d /\ source_rel (snd c) (snd d).

Definition state_bisim_candidate (v : ptree' E MN (S*A)) (w : ptree' E MN (S*B)) : Prop :=
  exists t u s, v = observe (run_state t s) /\ w = observe (run_state u s) /\ source_rel t u.

Local Notation heads_rel := (@ptree_stable_head_rel E MN (S*A) (S*B)
  (state_result_rel RR) state_bisim_candidate).

Lemma state_head_result_related s h1 h2 :
  @ptree_stable_head_rel (stateE S +' E) MN A B RR
    (@peutt_state (stateE S +' E) MN MF FI FC MX FO A B RR) h1 h2 ->
  stable_target_rel state_config_rel heads_rel (state_head_result s h1) (state_head_result s h2).
Proof.
  intro H. inversion H; subst; cbn [state_head_result stable_target_rel].
  - constructor. split; [reflexivity|assumption].
  - destruct e as [se|fe].
    + destruct (state_response se s) as [s' x]. split; [reflexivity|]. apply H0.
    + constructor. intro x. exists (k1 x), (k2 x), s.
      repeat split; try reflexivity. apply H0.
Qed.

Theorem state_machine_kernel_related c d :
  state_config_rel c d ->
  sem_lift (stable_target_rel state_config_rel heads_rel)
    (state_machine_kernel c) (state_machine_kernel d).
Proof.
  destruct c as [s t], d as [s' u]. intros [Hs Htu]. cbn in Hs, Htu. subst s'.
  unfold state_machine_kernel; cbn [fst snd]. eapply Hbind.
  - eapply peutt_state_hitting_lift;
      [exact Htu|apply handler_complete_front_hitting|apply handler_complete_front_hitting].
  - intros h1 h2 Hh. apply sem_lift_ret. apply state_head_result_related. exact Hh.
Qed.

Theorem state_machine_complete_related (Hzero : relational_zero FO) (Hlimit : relational_lub FO)
    c d mu nu :
  state_config_rel c d ->
  stable_hitting state_machine_kernel c mu ->
  stable_hitting state_machine_kernel d nu -> sem_lift heads_rel mu nu.
Proof.
  apply (stable_hitting_rel Hbind Hzero state_machine_kernel_related Hlimit).
Qed.
End StateSimulation.
