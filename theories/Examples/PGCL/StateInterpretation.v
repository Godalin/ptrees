(** Algebraic State elimination for the pGCL frontend. Distribution analysis
    is separate in Adequacy.v; this file relates actual program interpreters. *)
From Coq Require Import Utf8.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Fold.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder RelationalClosure.
From PTree.Eq Require Import PStruct Shallow PEutt Relation Bind Algebra Iter PTreeKernel.
From PTree.Interp Require Import State StateFacts StateIter Iteration IterationAlgebra
  FoldPTree StateFold StateFoldFacts HandlerFacts IterationUniform.
From PTree.Interp.Algebra Require Import Computation.
From PTree.Examples.PGCL Require Import Syntax Interpretation.
Set Implicit Arguments.
Unset Strict Implicit.

Section Lowering.
Context {S P : Type} {MN MF E : Type → Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI} `{MX : MixedMeasure MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variables (Hmixed : relational_mixed_bind NI FI MX)
  (Hzero : relational_zero FO) (Hlimit : relational_lub FO).
Variable coin : P → MN bool.
Local Notation W := (peutt (MF := MF)).
Local Notation structural :=
  (Relation.peutt_of_pstruct (relational_bind_of_laws FB) Hmixed Hzero Hlimit).
Local Notation result_rel := (λ sa s, sa = (s,tt)).

Local Lemma get_state s : W eq
  (@run_state S E MN S get s) (Ret (s,s)).
Proof.
  transitivity (Tau (@run_state S E MN S (Ret s) s)).
  - apply structural. exact (StateFacts.run_state_get (λ x, Ret x) s).
  - rewrite peutt_tau_l. apply structural. apply StateFacts.run_state_ret.
Qed.

Local Lemma put_state s t : W eq
  (@run_state S E MN unit (put t) s) (Ret (t,tt)).
Proof.
  transitivity (Tau (@run_state S E MN unit (Ret tt) t)).
  - apply structural. exact (StateFacts.run_state_put (λ x, Ret x) s t).
  - rewrite peutt_tau_l. apply structural. apply StateFacts.run_state_ret.
Qed.

Theorem elaborate_state (c : command S P) s :
  W result_rel (run_state (elaborate (E := E) coin c) s) (execute coin c s).
Proof.
  induction c in s |- *; cbn [elaborate execute].
  - setoid_rewrite (structural (StateFacts.run_state_ret tt s)).
    apply peutt_ret. reflexivity.
  - eapply peutt_of_hitting_lift.
    + apply ptree_stable_hitting_spin_zero. reflexivity.
    + apply ptree_stable_hitting_spin_zero. reflexivity.
    + apply Hzero.
  - setoid_rewrite (structural (StateFacts.run_state_bind get (λ s, put (update s)) s)).
    setoid_rewrite get_state.
    setoid_rewrite (Algebra.peutt_bind_ret_l).
    setoid_rewrite put_state. apply peutt_ret. reflexivity.
  - setoid_rewrite (structural (StateFacts.run_state_bind (elaborate coin c1)
      (λ _, elaborate coin c2) s)).
    eapply Bind.peutt_bind with (RR := result_rel).
    + apply IHc1.
    + intros [t []] u H; inversion H; subst. apply IHc2.
  - setoid_rewrite (structural (StateFacts.run_state_bind get
      (λ t, if test t then elaborate coin c1 else elaborate coin c2) s)).
    setoid_rewrite get_state. setoid_rewrite (Algebra.peutt_bind_ret_l).
    cbn [fst snd]. destruct (test s); [apply IHc1|apply IHc2].
  - setoid_rewrite (structural (StateFacts.run_state_bind (PTree.sample (coin probability))
      (λ v : bool, if v then elaborate coin c1 else elaborate coin c2) s)).
    setoid_rewrite <- (Algebra.peutt_sample_bind (coin probability)
      (λ v : bool, if v then execute coin c1 s else execute coin c2 s)).
    eapply Bind.peutt_bind with (RR := λ sb b, sb = (s,b)).
    + apply structural. apply pstruct_fold. cbn. constructor.
      intro b. apply pstruct_fold. cbn. constructor. reflexivity.
    + intros [t b] b' H; inversion H; subst. destruct b'; [apply IHc1|apply IHc2].
  - setoid_rewrite (structural (run_state_iter _ tt s)).
    eapply (peutt_iter_eventful_rel Hmixed Hzero Hlimit)
      with (SI := λ si s, si = (s,tt)).
    + intros [t []] u H; inversion H; subst.
      unfold state_iter_step. cbn [fst snd].
      setoid_rewrite (structural (StateFacts.run_state_bind get _ u)).
      setoid_rewrite get_state. setoid_rewrite (Algebra.peutt_bind_ret_l).
      cbn [fst snd]. destruct (test u).
      * setoid_rewrite (structural (StateFacts.run_state_bind (elaborate coin c)
          (λ _, Ret (inl tt)) u)).
        setoid_rewrite (Algebra.peutt_bind_assoc
          (relational_bind_of_laws FB) Hmixed Hzero Hlimit).
        eapply Bind.peutt_bind with (RR := result_rel).
        -- apply IHc.
        -- intros [v []] w Hw; inversion Hw; subst.
           setoid_rewrite (structural (StateFacts.run_state_ret (inl tt) w)).
           setoid_rewrite (Algebra.peutt_bind_ret_l).
           apply peutt_ret. constructor. reflexivity.
      * setoid_rewrite (structural (StateFacts.run_state_ret (inr tt) u)).
        setoid_rewrite (Algebra.peutt_bind_ret_l).
        apply peutt_ret. constructor. reflexivity.
    + reflexivity.
Qed.

(** The public monadic interpreter, not just the productive state eliminator,
    agrees with the explicit-state normal form. *)
Theorem run_execute (c : command S P) s :
  W eq (run (E := E) coin c s) (execute coin c s).
Proof.
  unfold run, PTree.fmap.
  assert (Hstate : W eq
    (interp_state (@PTree.trigger E MN) (elaborate coin c) s)
    (run_state (elaborate coin c) s)).
  { transitivity (interp (@PTree.trigger E MN)
      (run_state (elaborate coin c) s)).
    - apply (interp_state_run_state (QT := ptree_peutt_eq1 (FI := FI))
        (QE := ptree_peutt_equivalence)
        (ML := ptree_peutt_monad_laws Hmixed Hzero Hlimit)).
      exact (ptree_peutt_iteration_uniform Hmixed Hzero Hlimit).
    - exact (interp_ptree_identity Hmixed Hzero Hlimit _). }
  setoid_rewrite Hstate.
  setoid_rewrite <- (Algebra.peutt_bind_ret_r
    (relational_bind_of_laws FB) Hmixed Hzero Hlimit (execute coin c s)).
  eapply Bind.peutt_bind with (RR := result_rel).
  - apply elaborate_state.
  - intros [t []] u H; inversion H; subst. apply peutt_ret. reflexivity.
Qed.
End Lowering.
