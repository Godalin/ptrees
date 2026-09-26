(** Eventful iteration through a direct restart machine. Neither the loop
    state nor its result is placed in an auxiliary effect signature. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition IterationLaws.
From ITree.Basics Require Import Basics Monad.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder RelationalClosure.
From PTree.Eq Require Import PStruct PEutt Relation RelationalHitting StableHittingRelation
  PrimitiveStableHitting.
From PTree.Interp Require Import HandlerMachine IterationMachine IterationAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.

Section Relational.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variables (Hzero : relational_zero FO) (Hlimit : relational_lub FO).
Context {I J A B : Type}.
Variables (f : I -> ptree E MN (I+A)) (g : J -> ptree E MN (J+B))
  (SI : I -> J -> Prop) (RR : A -> B -> Prop).
Local Notation SR := (pstruct_iter_sum_rel SI RR).
Hypothesis Hstep : forall i j, SI i j -> peutt (MF := MF) SR (f i) (g j).
Local Notation W := (peutt (MF := MF) SR).

Definition iter_direct_states (s : ptree' E MN A) (v : ptree' E MN B) :=
  exists t u, s = observe (iter_active f t) /\ v = observe (iter_active g u) /\ W t u.
Local Notation HR := (@ptree_stable_head_rel E MN A B RR iter_direct_states).

Lemma iter_direct_kernel_related t u : W t u ->
  sem_lift (stable_target_rel W HR)
    (iter_machine_kernel f t) (iter_machine_kernel g u).
Proof.
  intro H. unfold iter_machine_kernel.
  eapply sem_lift_bind.
  - exact (peutt_hitting_lift H (handler_complete_front_hitting t)
      (handler_complete_front_hitting u)).
  - intros a b Hab. apply sem_lift_ret. destruct Hab.
    + destruct H0; cbn [iter_head_result].
      * apply Hstep. assumption.
      * constructor. assumption.
    + cbn [iter_head_result]. constructor. intro x.
      exists (k1 x), (k2 x). split; [reflexivity|split; [reflexivity|apply H0]].
Qed.

Theorem peutt_iter_active_rel t u : W t u ->
  peutt (MF := MF) RR (iter_active f t) (iter_active g u).
Proof.
  intro H. eapply peutt_coinduction with (sim := iter_direct_states).
  - intros s v [t' [u' [-> [-> Htu]]]].
    destruct (stable_hitting_exists (iter_machine_kernel f) t') as [mu Hmu].
    destruct (stable_hitting_exists (iter_machine_kernel g) u') as [nu Hnu].
    eapply stable_hitting_match_of_hitting_lift.
    + exact (iter_machine_hitting_sound (Directed := Directed) Hmu).
    + exact (iter_machine_hitting_sound (Directed := Directed) Hnu).
    + eapply (stable_hitting_rel (relational_bind_of_laws FB) Hzero
        iter_direct_kernel_related Hlimit); eassumption.
  - exists t,u. split; [reflexivity|split; [reflexivity|exact H]].
Qed.

Theorem peutt_iter_direct_rel i j : SI i j ->
  peutt (MF := MF) RR (PTree.iter f i) (PTree.iter g j).
Proof.
  intro Hij. change (peutt (MF := MF) RR (iter_active f (f i)) (iter_active g (g j))).
  apply peutt_iter_active_rel. apply Hstep. exact Hij.
Qed.
End Relational.

(** Ordinary setoid rewriting is a corollary of heterogeneous iteration.
    Register locally after supplying the frontier's relational certificates;
    do not ask global typeclass search to invent them. *)
Section Rewriting.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variables (Hzero : relational_zero FO) (Hlimit : relational_lub FO).

Lemma peutt_iter_Proper {I A} :
  Proper
    (pointwise_relation I (@peutt E MN MF FI FC MX FO (I+A) (I+A) eq) ==>
     eq ==> @peutt E MN MF FI FC MX FO A A eq)
    (@PTree.iter E MN A I).
Proof.
  intros f g H i j ->.
  eapply (peutt_iter_direct_rel Hzero Hlimit) with (SI := eq).
  - intros x y ->. eapply peutt_rel_mono.
    + intros v w ->. destruct w; constructor; reflexivity.
    + apply H.
  - reflexivity.
Qed.
End Rewriting.

Section Uniform.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variables (Hmixed : relational_mixed_bind NI FI MX)
  (Hzero : relational_zero FO) (Hlimit : relational_lub FO).

Theorem ptree_peutt_iteration_uniform :
  @iteration_uniform (ptree E MN) Monad_ptree MonadIter_ptree (ptree_peutt_eq1 (FI := FI)).
Proof.
  intros I J A f g h Hsquare i.
  change (peutt (FI := FI) eq (PTree.iter f i) (PTree.iter g (h i))).
  eapply (peutt_iter_direct_rel Hzero Hlimit) with (SI := fun i j => h i = j); [|reflexivity].
  intros x y <-. eapply IterationAlgebra.peutt_relation_right; [|exact (Hsquare x)].
  apply (Relation.peutt_of_pstruct (relational_bind_of_laws FB) Hmixed Hzero Hlimit).
  apply pstruct_return_map. intros [j|a]; constructor; reflexivity.
Qed.
End Uniform.
