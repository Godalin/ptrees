(** Transition Relation of the Probabilistic Trees

    This file contains the theory of *Probabilistic
    Bisimulation* of [ptree]s.
 *)

Set Warnings "-notation-incompatible-prefix".
Set Warnings "-ambiguous-paths".

Require Import Utf8.
Require Import Program Morphisms.

From Coinduction Require Import all.
From RelationAlgebra Require Import
     monoid
     kat
     kat_tac
     prop
     rel
     srel
     comparisons
     rewriting
     normalisation.
From mathcomp Require Import ssreflect ssrbool eqtype seq finset ssralg order.

From PTree.Core Require Import PTreeDefinitionNew Utils.
From PTree.Prob Require Import RatSubTypes DiscreteMC.
From PTree.Eq Require Import EquNew ShallowNew.



#[local] Ltac inv H := inversion H; clear H; subst.
#[local] Tactic Notation "step" := __step_equ.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_equ H.

(* To use the relation algebra library,
  the universe check should be unset. *)
Unset Universe Checking.

Section Trans.
Import PTree.
Import EquNotations.
#[local] Open Scope ptree_scope.

Context {E : Type → Type}.
Context {M : Type → Type}.
Context `{DiscreteInterface M}.
Context {R : Type}.

#[local] Notation S' := (ptree' E M R).
#[local] Notation S := (ptree E M R).



Definition SS : EqType :=
  {| type_of := S; Eq := equ eq |}.

(** Labels of the LTS.
    (* TODO *) [prb] can contain "density" in continuous cases. *)

Inductive label : Type :=
  | tau
  | obs {X : Type} (e : E X) (v : X)
  | val {X : Type} (v : X).

Variant is_val : label → Prop :=
  | Is_val : forall X (x : X), is_val (val x).

Lemma is_val_tau : ¬ is_val tau.
Proof. intros Contra. inversion Contra. Qed.

Lemma is_val_obs {X} (e : E X) x : ¬ is_val (obs e x).
Proof. intros Contra. inversion Contra. Qed.



Import Enum.
Import NonnegQNotations.
Import GRing.Theory.


Inductive trans_ : label → ℚ≥0 → hrel S' S' :=
  | StepVal r μ k
    (q: ℚ≥0) : trans_ (val r) q (RetF r) (ProbF0 μ k)
  | StepTau t u
    (q: ℚ≥0) : t ≅ u ->
      trans_ tau q (TauF t) (observe u)
  | StepObs {X} (e : E X) k x t
    (q: ℚ≥0) : k x ≅ t ->
      trans_ (obs e x) q (VisF e k) (observe t)
  | StepPrb {X : eqType} (μ : M X) k x p t
    : disc_mass x μ = p ->
      k x ≅ t ->
      trans_ tau p (ProbF μ k) (observe t).
Hint Constructors trans_ : core.

Definition transR l p : hrel S S
  := fun u v => trans_ l p (observe u) (observe v).

Ltac FtoObs :=
  match goal with
  | |- trans_ _ _ _ ?t =>
    change t with (observe {| _observe := t |})
  end.

Lemma trans_any_poss {l p t t'} (p': ℚ≥0) (not_prob: ~~ (IsProbF t)): trans_ l p t t' -> trans_ l p' t t'.
Proof.
  move => h. destruct t ; inversion h.
  - constructor.
  - econstructor; auto.
  - dependent destruction H4. dependent destruction H5.
    econstructor. rewrite -H6 //=.
  - rewrite /IsProbF //= in not_prob.
Qed.

#[local] Instance trans_equ_aux1 l p t
  : Proper (going (equ eq) ==> flip impl) (trans_ l p t).
Proof. intros u u' Heq. intros TR.
  inv Heq. rename H0 into EQU.
  step in EQU. revert u EQU.
  dependent induction TR.
  - intros. dependent destruction EQU.
    econstructor.
  - intros. FtoObs. constructor. rewrite H0.
    rewrite (ptree_eta u). symmetry. step. auto.
  - intros. FtoObs. constructor. rewrite H0.
    rewrite (ptree_eta t). symmetry. step. auto.
  - intros. FtoObs. econstructor; eauto.
    rewrite H1. rewrite (ptree_eta t). symmetry. step. auto.
Qed.

#[local] Instance trans_equ_aux2 l p
  : Proper (going (equ eq) ==> going (equ eq) ==> impl) (trans_ l p).
Proof. intros t1 t2 Heqt u1 u2 Hequ TR.
  rewrite <- Hequ. clear u2 Hequ.
  inv Heqt. rename H0 into Heqt. step in Heqt.
  revert t2 Heqt. dependent induction TR.
  - intros. dependent destruction Heqt.
    constructor.
  - intros. dependent destruction Heqt.
    constructor. symmetry. transitivity t.
    symmetry. all: auto.
  - intros. dependent destruction Heqt.
    constructor. symmetry. rewrite <- H0.
    apply REL.
  - intros. dependent destruction Heqt.
    econstructor.
    rewrite <- REL. eassumption.
    symmetry. rewrite <- H1. apply RELk.
Qed.

#[global] Instance trans_equ_ l p
  : Proper (going (equ eq) ==> going (equ eq) ==> iff) (trans_ l p).
Proof. intros ?? EQt ?? EQu. split; intro TR.
  - eapply trans_equ_aux2; eauto.
  - symmetry in EQt. symmetry in EQu.
    eapply trans_equ_aux2; eauto.
Qed.

#[global] Instance trans_equ l p
  : Proper (equ eq ==> equ eq ==> iff) (transR l p).
Proof. intros ?? EQt ?? EQu. unfold transR.
  rewrite EQt. rewrite EQu. reflexivity.
Qed.

Definition trans l p : srel SS SS :=
  {| hrel_of := transR l p : hrel SS SS |}.

Lemma trans__trans : forall l p t u,
  trans_ l p (observe t) (observe u) = trans l p t u.
Proof. reflexivity. Qed.

Lemma transR_trans : forall l p t u,
  transR l p t u = trans l p t u.
Proof. reflexivity. Qed.



Definition etrans l p : srel SS SS :=
  match l with
  | tau => (cup (trans l p) 1)
  | _ => trans l p
  end.

Definition wtrans l : srel SS SS :=
  (trans tau 1)^* ⋅ etrans l 1 ⋅ (trans tau 1)^*.

Definition pwtrans l : srel SS SS :=
  (trans tau 1)^* ⋅ trans l 1 ⋅ (trans tau 1)^*.

Definition tautrans : srel SS SS :=
  (trans tau 1)^+.

End Trans.



Section Trans_relation.

Import Enum.
Import NonnegQNotations.
Import Coq.Init.Specif.

Fixpoint transAll {E} {R} (t : ptree E Enum R)
    (tlist : Enum (label * ptree E Enum R)) : Prop :=
  match tlist with
  | [::] => True
  | i :: tlist' => trans (fst (snd i)) (fst i) t (snd (snd i)) ∧ transAll t tlist'
  end.

Definition transAllPrb {E X} (tlist : Enum (ptree E Enum X)) : ℚ≥0 :=
  sumq (unzip1 tlist).

Fixpoint relateAll {X Y} (R : rel X Y) (x : X) (ys : seq Y) : Prop :=
  match ys with
  | [::] => True
  | y :: ys' => R x y ∧ relateAll R x ys'
  end.

Lemma relateAll_sub {X Y} (R S : rel X Y) (x : X) (ys : seq Y)
  : (∀ x y, R x y → S x y) → relateAll R x ys → relateAll S x ys.
Proof. elim: ys => [//|y ys IH //= H] [Hxy Hxys]. auto. Qed.

Lemma relateAll_trans {X} (R : relation X) `{Transitive _ R}
  : ∀ (x y : X) (zs : seq X), R x y → relateAll R y zs → relateAll R x zs.
Proof. intros. induction zs.
  auto. simpl in H1. destruct H1 as [Rya RAyzs].
  simpl. split. etransitivity; eauto.
  apply IHzs. eauto.
Qed.

Lemma relateAll_iff_forall_map {X Z: Type} {Y: eqType} {R : rel X Z} {f: Y -> Z}
   {x : X} {z : seq Y}: relateAll R x [seq f i | i <- z] <-> ∀i, i \in z -> R x (f i).
Proof. split.
  - elim: z => [//=|a l IH h i hi]. move : h => [Rxa rl].
    rewrite in_cons in hi. move : hi => /orP [/eqP i_eq_a | i_in_l].
    + rewrite i_eq_a. exact: Rxa.
    + exact: IH rl i i_in_l.
  - elim: z => [//=|a l IH h]. split.
    + apply h. rewrite in_cons eq_refl //=.
    + apply IH. move => i hi. apply h. rewrite in_cons hi orbT //=.
Qed.

Lemma relateAll_iff_forall {X: Type} {Y: eqType} (R : rel X Y)
   {x : X} {z : seq Y}: relateAll R x z <-> ∀i, i \in z -> R x i.
Proof.
  have hm:=@relateAll_iff_forall_map X Y Y R (fun x => x) x z.
  rewrite map_id //= in hm.
Qed.

Lemma relateAll_subset {X: Type} {Y: eqType} (R : rel X Y)
   {x : X} {z1 z2 : seq Y} (subset : {subset z1 <= z2}) : relateAll R x z2 → relateAll R x z1.
Proof.
  rewrite relateAll_iff_forall relateAll_iff_forall. move => r2 i hi. apply r2. exact: subset hi.
Qed.

Lemma relateAll_map_subset {X Z: Type} {Y: eqType} {R : rel X Z} {f: Y -> Z}
   {x : X} {z1 z2 : seq Y} (subset : {subset z1 <= z2}) : relateAll R x [seq f i | i <- z2] → relateAll R x [seq f i | i <- z1].
Proof.
  rewrite relateAll_iff_forall_map relateAll_iff_forall_map. move => r2 i hi. apply r2. exact: subset hi.
Qed.

Lemma relateAll_app {X Y: Type} {R : rel X Y}
   {x : X} (z1 z2 : seq Y) : relateAll R x (z1 ++ z2) <-> relateAll R x z1 /\ relateAll R x z2.
Proof.
  elim : z1 => [//=|a z1 IH].
  - split. move => i. split; auto. move => [_ i]. exact: i.
  - rewrite cat_cons /relateAll -/relateAll IH.
    split. move => [b [c d]]. split. split. all: try assumption.
    move => [[b c] d]. split. assumption. split. all: try assumption.
Qed.


Lemma transAll_iff_forall_map {X : eqType} {E} {R} {f: X -> (ℚ≥0 * (label * ptree E Enum R))}
  {t : ptree E Enum R} {t' : seq X} : transAll t [seq f i | i <- t'] <-> ∀x, x \in t' -> trans (fst (snd (f x))) (fst (f x)) t (snd (snd (f x))).
Proof.
  split.
  - elim: t' => [//=|a l IH h i hi]. rewrite map_cons /transAll in h.
    move : h => [Rxa rl]. rewrite in_cons in hi. move : hi => /orP [/eqP i_eq_a | i_in_l].
    + rewrite i_eq_a. exact: Rxa.
    + exact: IH rl i i_in_l.
  - elim: t' => [//=|a l IH h]. split.
    + apply h. rewrite in_cons eq_refl //=.
    + apply IH. move => i hi. apply h. rewrite in_cons hi orbT //=.
Qed.

Lemma transAll_subset_map {X : eqType} {E} {R} {f: X -> (ℚ≥0 * (label * ptree E Enum R))}
  {t : ptree E Enum R} {t1 t2 : seq X} (subset: {subset t1 <= t2}) : transAll t [seq f i | i <- t2] -> transAll t [seq f i | i <- t1].
Proof.
  rewrite transAll_iff_forall_map transAll_iff_forall_map.
  move => h1 x hx. apply h1. exact: subset hx.
Qed.


Program Fixpoint to_transable_index {E} {R} {X : eqType} {t : ptree E Enum R} {f: X -> nnQ * (label * ptree E Enum R)}
    {xs : seq X} (tr: transAll t [seq f i | i <- xs]) : seq {x : X | (let i := f x in trans (fst (snd i)) (fst i) t (snd (snd i))) } :=
  match xs with
  | [::] => [::]
  | x :: xs' => (exist _ x _) :: (to_transable_index (xs:= xs') _)
  end.
Next Obligation.
  rewrite map_cons in tr. exact: proj1 tr.
Qed.
Next Obligation.
  rewrite map_cons in tr. exact: proj2 tr.
Qed.

(*
Lemma transAll_Prob_Cons {E} {X : eqType} {Y} {k : X → ptree E Enum Y} (x : Enum X) (p : ℚ≥0 * X) (l : seq X)
  : transAll tau (Prob x k) [seq enumk x k x0  | x0 <- l] -> transAll tau (Prob (p :: x) k) [seq enumk (p :: x) k x0 | x0 <- l].
Proof.
  move => ih. induction l. rewrite //=.
  rewrite map_cons /transAll in ih. destruct ih.
  have ih1 := IHl H0. clear IHl H0.
  rewrite map_cons /transAll. split.
  econstructor. reflexivity. reflexivity. exact ih1.
Qed.

Lemma transAll_Prob {E} {X : eqType} {Y}
  : ∀ (μ : Enum X) (k : X → ptree E Enum Y), transAll tau (Prob μ k) [seq enumk μ k x | x <- supp μ].
Proof.
  move => μ k. elim : μ => [//|p x ih]. rewrite /supp /unzip2 filter_cons.
  case: (fst p == 0).
  - rewrite //=. rewrite /enumk. eapply transAll_Prob_Cons. exact: ih.
  - rewrite //=.
    case: (snd p \in [seq snd i  | i <- x  & fst i != 0]).
    (* p in [seq snd i  | i <- x] *)
    + rewrite /enumk. eapply transAll_Prob_Cons. exact: ih.

    (* p not in [seq snd i  | i <- x] *)
    + rewrite /enumk map_cons /transAll. split.
      econstructor. reflexivity. reflexivity.
      eapply transAll_Prob_Cons. exact: ih.
Qed.



Lemma transAll_Prob_tau {E} {X : eqType} {Y} {l} {s}
  : ∀ (μ : Enum X) (k : X → ptree E Enum Y),
    transAll l (Prob μ k) s → s = [::] ∨ l = tau.
Proof. intros. induction s. left; auto. destruct a. right.
  simpl in H. destruct H as [Htrans ?].
  inversion Htrans. auto.
Qed.
*)
End Trans_relation.



Module Import TransNotations.
Infix "---[ l ; p ]-->" := (trans l p) (at level 70).
End TransNotations.
