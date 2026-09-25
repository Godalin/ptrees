(** Explicit behavioral Monad/Eq1 and pure-map iteration proofs for PTree.
    No global Eq1 selection and no new algebraic capability are registered. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms RelationClasses Program.Equality.
From ExtLib.Structures Require Import Monad.
From ITree.Basics Require Import Basics Monad.
From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinition IterationLaws.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder RelationalClosure.
From PTree.Eq Require Import PStruct Shallow PEutt Relation Bind Algebra Iter.
From PTree.Interp Require Import Iteration.
Set Implicit Arguments.
Unset Strict Implicit.
Local Notation "` R" := (elem R) (at level 10).

Section ReturnMap.
Context {E MN : Type -> Type} {A B : Type}.
Variable f : A -> B.
Variable RR : A -> B -> Prop.
Hypothesis Hf : forall a, RR a (f a).
Local Definition map_candidate (t : ptree E MN A) (u : ptree E MN B) :=
  u = PTree.fmap f t.

Lemma pstruct_return_map (input : ptree E MN A) :
  pstruct RR input (PTree.fmap f input).
Proof.
  assert (H : forall t u, map_candidate t u -> pstruct RR t u).
  { unfold pstruct. coinduction CH CIH. intros t u ->.
    change (pstructF RR (` CH) (observe t) (observe (PTree.fmap f t))).
    unfold PTree.fmap. rewrite observe_bind.
    destruct (observe t); cbn; constructor; try apply Hf.
    - apply CIH. reflexivity.
    - intro x. apply CIH. reflexivity.
    - intro x. apply CIH. reflexivity. }
  apply H. reflexivity.
Qed.
End ReturnMap.

Section Laws.
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


Local Notation W A B RR := (@peutt E MN MF FI FC MX FO A B RR).

Definition ptree_peutt_eq1 : Eq1 (ptree E MN) := fun A => W A A eq.
Definition ptree_peutt_equivalence :
  @Eq1Equivalence (ptree E MN) Monad_ptree ptree_peutt_eq1.
Proof. intro A. apply peutt_equivalence. Defined.

Definition ptree_peutt_monad_laws :
  @MonadLawsE (ptree E MN) ptree_peutt_eq1 Monad_ptree.
Proof.
  constructor; intros; unfold eq1, ptree_peutt_eq1;
    cbn [Monad.bind Monad.ret Monad_ptree].
  - apply (Algebra.peutt_bind_ret_l (relational_bind_of_laws FB) Hmixed Hzero Hlimit).
  - apply (Algebra.peutt_bind_ret_r (relational_bind_of_laws FB) Hmixed Hzero Hlimit).
  - apply (Algebra.peutt_bind_assoc (relational_bind_of_laws FB) Hmixed Hzero Hlimit).
  - intros x y Hxy k h Hkh. eapply Bind.peutt_bind with (RR := eq).
    + exact Hxy.
    + intros a b ->. apply Hkh.
Defined.

(** Right endpoint transport for an arbitrary heterogeneous relation.
    This is an application of existing hitting-bisimulation composition. *)
Local Lemma peutt_relation_right {A B} (RR : A -> B -> Prop)
    (t : ptree E MN A) (u v : ptree E MN B) :
  W A B RR t u -> W B B eq u v -> W A B RR t v.
Proof.
  intros Htu Huv. unfold peutt, peutt_state in Htu, Huv |- *.
  eapply stable_hitting_bisim_compose; [|exact Htu|exact Huv].
  intros sim12 sim23 sim13 Hsim h1 h3 [h2 [H12 H23]].
  dependent destruction H12; dependent destruction H23.
  - constructor. subst. assumption.
  - constructor. intro x. apply Hsim. eauto.
Qed.

(** Specified-carrier uniformity. This deliberately is not packaged as the
    Eq1-wide [iteration_uniform]: the protocol proof uses I+A as a visible
    response type. See the independently checked client-universe boundary. *)
Theorem peutt_iter_uniform {I J A}
    (f : I -> ptree E MN (I+A)) (g : J -> ptree E MN (J+A)) (h : I -> J) :
  (forall i, W (J+A) (J+A) eq
    (PTree.bind (f i) (fun v => Ret (iteration_map h v))) (g (h i))) ->
  forall i, W A A eq (PTree.iter f i) (PTree.iter g (h i)).
Proof.
  intros Hsquare i.
  eapply (peutt_iter_eventful_rel Hmixed Hzero Hlimit)
    with (SI := fun i j => h i = j); [|reflexivity].
  intros x y <-. eapply peutt_relation_right; [|exact (Hsquare x)].
  apply structural. apply pstruct_return_map.
  intros [j|a]; constructor; reflexivity.
Qed.

(** Fixed point with the administrative retry Tau removed behaviorally. *)
Theorem ptree_peutt_iter_unfold {I A} (step : I -> ptree E MN (I+A)) i :
  W A A eq (PTree.iter step i)
    (PTree.bind (step i) (fun v => match v with
      | inl j => PTree.iter step j | inr a => Ret a end)).
Proof.
  eapply peutt_trans.
  - apply (Iter.peutt_iter_unfold (relational_bind_of_laws FB) Hmixed Hzero Hlimit).
  - eapply Bind.peutt_bind with (RR := eq).
    + apply peutt_refl.
    + intros x y ->. destruct y; [apply peutt_tau_l|apply peutt_refl].
Qed.

Theorem ptree_peutt_iter_tau_step {I A} (step : I -> ptree E MN (I+A)) i :
  W A A eq (PTree.iter (fun j => Tau (step j)) i) (PTree.iter step i).
Proof.
  apply (peutt_iter_eventful Hmixed Hzero Hlimit). intro j. apply peutt_tau_l.
Qed.

(** The finite number of inserted Taus may depend on the state and need
    not have a uniform bound across an infinite run. *)
Theorem ptree_peutt_iter_finite_stutter {I A}
    (step : I -> ptree E MN (I+A)) (delay : I -> nat) i :
  W A A eq
    (PTree.iter (fun j => Nat.iter (delay j) (fun t => Tau t) (step j)) i)
    (PTree.iter step i).
Proof.
  apply (peutt_iter_eventful Hmixed Hzero Hlimit). intro j.
  induction (delay j) as [|n IH]; cbn.
  - apply peutt_refl.
  - eapply peutt_trans; [apply peutt_tau_l|exact IH].
Qed.
End Laws.
