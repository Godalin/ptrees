From PTree.Prob.Interface Require Import RelationalClosure.
From PTree.Eq Require Import Relation Shallow PStruct.
(** Role: Backend-independent setoid rewriting, derived from generic bind.
    No completion representation or external validation model is selected here. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder.
From PTree.Eq Require Import PEutt Bind.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Shallow equations do not need a structural-to-behavioral limit theorem.
    Only the interpretation operations and frontier CoreLaws are required. *)
Section ShallowAlgebra.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}.

Lemma peutt_observe_eq {A} (t u : ptree E MN A) :
  observe t = observe u -> @peutt E MN MF FI FC MX FO A A eq t u.
Proof.
  intro H. pose proof (@peutt_refl E MN MF FI FC MX FO A u) as Hu.
  unfold peutt in Hu |- *. rewrite H. exact Hu.
Qed.

Theorem peutt_bind_ret_l {A B} (a : A) (k : A -> ptree E MN B) :
  @peutt E MN MF FI FC MX FO B B eq (PTree.bind (Ret a) k) (k a).
Proof. apply peutt_observe_eq. reflexivity. Qed.

(** Constructor distribution is shallow: no native laws, termination or
    relational-limit closure is needed. *)
Theorem peutt_bind_tau {A B} (t : ptree E MN A) (k : A -> ptree E MN B) :
  peutt (MF := MF) eq (PTree.bind (Tau t) k) (Tau (PTree.bind t k)).
Proof. apply peutt_observe_eq. reflexivity. Qed.

Theorem peutt_bind_vis {A B X} (e : E X)
    (h : X -> ptree E MN A) (k : A -> ptree E MN B) :
  peutt (MF := MF) eq (PTree.bind (Vis e h) k)
    (Vis e (fun x => PTree.bind (h x) k)).
Proof. apply peutt_observe_eq. reflexivity. Qed.

Theorem peutt_bind_prob {A B X} (mu : MN X)
    (h : X -> ptree E MN A) (k : A -> ptree E MN B) :
  peutt (MF := MF) eq (PTree.bind (Prob mu h) k)
    (Prob mu (fun x => PTree.bind (h x) k)).
Proof. apply peutt_observe_eq. reflexivity. Qed.

Theorem peutt_fmap_ret {A B} (f : A -> B) (a : A) :
  peutt (E := E) (MF := MF) eq (PTree.fmap f (Ret a)) (Ret (f a)).
Proof. apply peutt_observe_eq. reflexivity. Qed.

Theorem peutt_fmap_tau {A B} (f : A -> B) (t : ptree E MN A) :
  peutt (MF := MF) eq (PTree.fmap f (Tau t)) (Tau (PTree.fmap f t)).
Proof. apply peutt_observe_eq. reflexivity. Qed.

Theorem peutt_fmap_vis {A B X} (f : A -> B) (e : E X) (h : X -> ptree E MN A) :
  peutt (MF := MF) eq (PTree.fmap f (Vis e h))
    (Vis e (fun x => PTree.fmap f (h x))).
Proof. apply peutt_observe_eq. reflexivity. Qed.

Theorem peutt_fmap_prob {A B X} (f : A -> B) (mu : MN X) (h : X -> ptree E MN A) :
  peutt (MF := MF) eq (PTree.fmap f (Prob mu h))
    (Prob mu (fun x => PTree.fmap f (h x))).
Proof. apply peutt_observe_eq. reflexivity. Qed.
End ShallowAlgebra.

(** Native sampling algebra. The frontier and native carriers are arbitrary;
    mapping additionally needs mixed unit and node-bind compatibility, not
    commutativity or a particular completion representation. *)
Section SamplingAlgebra.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MO : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.

Theorem peutt_sample_bind {X A} (mu : MN X) (k : X -> ptree E MN A) :
  peutt (MF := MF) eq (PTree.bind (Prob mu (fun x => Ret x)) k) (Prob mu k).
Proof.
  eapply peutt_trans; [apply peutt_bind_prob|].
  eapply peutt_prob with (XR := eq).
  - apply sem_lift_refl. intro x. reflexivity.
  - intros x y ->. apply peutt_bind_ret_l.
Qed.

Context `{MU : @MixedMeasureUnitLaws MN MF NI FI MX}
  `{NB : @MixedMeasureNodeBindLaws MN MF NI FI MX}.

Theorem peutt_prob_map {X Y A} (mu : MN X) (f : X -> Y) (k : Y -> ptree E MN A) :
  peutt (MF := MF) eq (Prob mu (fun x => k (f x)))
    (Prob (sem_bind mu (fun x => sem_ret (f x))) k).
Proof.
  transitivity (Prob mu (fun x => Prob (sem_ret (f x)) k)).
  - eapply peutt_prob with (XR := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. apply peutt_sym, peutt_prob_ret.
  - apply peutt_prob_flatten.
Qed.

Theorem peutt_sample_map {X A} (mu : MN X) (f : X -> A) :
  peutt (E := E) (MF := MF) eq (Prob mu (fun x => Ret (f x)))
    (Prob (sem_bind mu (fun x => sem_ret (f x))) (fun a => Ret a)).
Proof. exact (peutt_prob_map mu f (fun a => Ret a)). Qed.
End SamplingAlgebra.

Section Algebra.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{BindOrd : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MixedOrd : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.

#[global] Instance peutt_bind_Proper {A B} :
  Proper
    (@peutt E MN MF FI FC MX FO A A eq ==>
     pointwise_relation A (@peutt E MN MF FI FC MX FO B B eq) ==>
     @peutt E MN MF FI FC MX FO B B eq)
    (@PTree.bind E MN A B).
Proof.
  intros t1 t2 Ht k1 k2 Hk.
  eapply peutt_bind with (RR := eq).
  - exact Ht.
  - intros x1 x2 ->. exact (Hk x2).
Qed.

#[global] Instance peutt_fmap_Proper {A B} (f : A -> B) :
  Proper
    (@peutt E MN MF FI FC MX FO A A eq ==>
     @peutt E MN MF FI FC MX FO B B eq)
    (PTree.fmap f).
Proof.
  intros t1 t2 Ht. unfold PTree.fmap.
  eapply peutt_bind with (RR := eq).
  - exact Ht.
  - intros x1 x2 ->. apply peutt_refl.
Qed.
End Algebra.

(** Elementary structural equations over any relationally continuous frontier.
    The four ordinary probability certificates are explicit; no PTree theorem
    is assumed and no global instance search is extended. *)
Section RelationalAlgebra.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}.
Variable Hbind : relational_bind FI.
Variable Hmixed : relational_mixed_bind NI FI MX.
Variable Hzero : relational_zero FO.
Variable Hlimit : relational_lub FO.

Theorem peutt_bind_ret_r {A} (t : ptree E MN A) :
  @peutt E MN MF FI FC MX FO A A eq
    (PTree.bind t (fun x => Ret x)) t.
Proof.
  apply (Relation.peutt_of_pstruct Hbind Hmixed Hzero Hlimit).
  apply pstruct_bind_ret_r.
Qed.

Theorem peutt_bind_assoc {A B C}
    (t : ptree E MN A) (k : A -> ptree E MN B)
    (h : B -> ptree E MN C) :
  @peutt E MN MF FI FC MX FO C C eq
    (PTree.bind (PTree.bind t k) h)
    (PTree.bind t (fun x => PTree.bind (k x) h)).
Proof.
  apply (Relation.peutt_of_pstruct Hbind Hmixed Hzero Hlimit).
  apply pstruct_bind_assoc.
Qed.

Theorem peutt_fmap_id {A} (t : ptree E MN A) :
  @peutt E MN MF FI FC MX FO A A eq
    (PTree.fmap (fun x => x) t) t.
Proof. unfold PTree.fmap. apply peutt_bind_ret_r. Qed.

Theorem peutt_fmap_compose {A B C}
    (f : A -> B) (g : B -> C) (t : ptree E MN A) :
  @peutt E MN MF FI FC MX FO C C eq
    (PTree.fmap g (PTree.fmap f t))
    (PTree.fmap (fun x => g (f x)) t).
Proof.
  apply (Relation.peutt_of_pstruct Hbind Hmixed Hzero Hlimit). unfold PTree.fmap.
  eapply pstruct_trans.
  - apply pstruct_bind_assoc.
  - eapply pstruct_bind with (RA := eq) (RB := eq).
    + intros x1 x2 ->. apply observe_eq_pstruct.
      exact (observing_observe (bind_ret_ (f x2) (fun y => Ret (g y)))).
    + apply pstruct_refl.
Qed.

Theorem peutt_fmap_bind {A B C}
    (f : B -> C) (t : ptree E MN A) (k : A -> ptree E MN B) :
  @peutt E MN MF FI FC MX FO C C eq
    (PTree.fmap f (PTree.bind t k))
    (PTree.bind t (fun x => PTree.fmap f (k x))).
Proof. unfold PTree.fmap. apply peutt_bind_assoc. Qed.

End RelationalAlgebra.
