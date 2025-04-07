(** Probabilistic Strong Simulation Relation *)
Set Warnings "-ambiguous-paths".
Unset Universe Checking.

Require Import Utf8.
Require Import Program Morphisms.

From Coinduction Require Import all.
From RelationAlgebra Require Import rel srel.
From mathcomp Require Import ssreflect ssrbool eqtype seq finset ssralg order.

From PTree.Core Require Import PTreeDefinitionNew Utils.
From PTree.Prob Require Import RatSubTypes DiscreteMC.
From PTree.Eq Require Import ShallowNew EquNew Trans.



Section PSSim.
Import Enum.
Import NonnegQNotations.
Import GRing.Theory Order.Theory.
Import EquNotations.

#[local] Notation ptree E := (ptree E Enum).
#[local] Notation ptree' E R := (ptree' E Enum R).

Section experiment.
Context {E F : Type → Type} {X Y : Type}.

(** Goal: define a prop: [R t u] is a simulation, or part of the prop
    t -- R ---- u
    |         | | |
  l |         p q r l
    |         | | |
    v         v v v
    t'-- R -- u'u'u'
  *)

Variant pssim_cond REL (t' : ptree E X) (l' : label) (p : ℚ≥0)
  : ptree' F Y → Prop :=
  | PSSimRetF
    : ∀ r u',
        trans l' p (Ret r) u'
      → REL t' u'
      → pssim_cond REL t' l' p (RetF r)
  | PSSimTauF
    : ∀ t u',
        trans l' p (Tau t) u'
      → REL t' u'
      → pssim_cond REL t' l' p (TauF t)
  | PSSimVisF
    : ∀ X' (e : F X') k u',
        trans l' p (Vis e k) u'
      → REL t' u'
      → pssim_cond REL t' l' p (VisF e k)
  | PSSimProbF
    : ∀ (X' : eqType) (μ : Enum X') (k : X' → ptree F Y) (s : seq X'),
        uniq s
      → {subset s <= supp μ}
      → transAll l' (Prob μ k) [seq enumk μ k x | x <- s]
      → relateAll REL t' [seq k x | x <- s]
      → p <= mass μ s
      → pssim_cond REL t' l' p (ProbF μ k).

Lemma sub_pssim_cond (R S : rel (ptree E X) (ptree F Y))
    t' (l : @label F) p u
  : (∀ x y, R x y → S x y) → pssim_cond R t' l p u → pssim_cond S t' l p u.
Proof. intros. inversion H0.
  - econstructor. apply H1. auto.
  - econstructor. apply H1. auto.
  - econstructor. apply H1. auto.
  - econstructor. apply H1. all: auto.
    apply (relateAll_sub R S); auto.
Qed.

Lemma pssim_cond_char : ∀ (REL : rel (ptree E X) (ptree F Y)) t' l p u,
    pssim_cond REL t' l p u
  → ∃ (u's : Enum (ptree F Y)),
      transAll l (go u) u's
    ∧ relateAll REL t' [seq snd p | p <- u's]
    ∧ p <= transAllPrb u's.
Proof. intros REL t' l p u H. inversion H; subst.
  - exists [:: (p, u')]; repeat split; simpl.
    inversion H0; subst; auto. assumption.
    unfold transAllPrb, foldr. simpl.
    rewrite addr0. rewrite le_refl. auto.
  - exists [:: (p, u')]; repeat split; simpl.
    inversion H0; subst; auto. assumption.
    unfold transAllPrb, foldr. simpl.
    rewrite addr0. rewrite le_refl. auto.
  - exists [:: (p, u')]; repeat split; simpl.
    inversion H0; subst. dependent destruction H7.
    econstructor. rewrite -> H5. apply observe_equ_eq.
    assumption. assumption.
    unfold transAllPrb, foldr. simpl.
    rewrite addr0. rewrite le_refl. auto.
  - exists (map (enumk μ k) s); repeat split; simpl.
    apply H2. rewrite <- map_comp. exact H3.
    apply (le_trans H4). unfold transAllPrb, unzip1.
    rewrite <- map_comp. unfold ssrfun.comp, fst, mass. simpl.
    rewrite le_refl. reflexivity.
Qed.

End experiment.



(** [pss] is the monotone function for probabilistic strong simulation  *)

#[program]
Definition pss {E F : Type → Type}
    {X Y : Type} (L : rel (@label E) (@label F))
  : mon (ptree E X → ptree F Y → Prop)
  := {| body R t u := ∀ l (p : ℚ≥0) t',
        trans l p t t' → ∃ l',
          L l l' ∧ pssim_cond R t' l' p (observe u)
     |}.
Next Obligation.
  destruct (H0 l p t' H1) as [l' [RL HCond]].
  exists l'. split; auto. apply (sub_pssim_cond x y); auto.
Defined.



(** [pssim] is the probabilistic similarity, which is defined as
    the greatest fixpoint of the monotone function [pss] *)

Definition pssim {E F X Y} L := (gfp (@pss E F X Y L)).

End PSSim.



(** pss tactics *)

Ltac __step_pssim := step.
#[local] Tactic Notation "step" := __step_pssim.

Ltac __step_in_pssim H :=
  match type of H with
  | context [@pssim ?E ?F ?X ?Y ?RL] =>
      unfold pssim in H; apply (gfp_pfp (pss RL)) in H;
      fold (@pssim E F X Y RL) in H
  | _ => fail "Fail to step pssim"
  end.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_pssim H.

#[local] Tactic Notation "step" "equ" "in" ident(H) :=
  __step_in_equ H.

Ltac __use_pssim Hpssim Htrans :=
  apply Hpssim in Htrans;
  let l := fresh "l'" in
  let RL := fresh "RL" in
  let Hpssim_cond := fresh Hpssim "Cond" in
  destruct Htrans as [l [RL Hpssim_cond]].
Tactic Notation "use" "pssim" "with" ident(Hpssim) ident(Htrans) :=
  __use_pssim Hpssim Htrans.



(** pss notation *)
Module Import PSSimNotations.
Notation "` R" := (elem R) (at level 10).

Infix "≲p" := (pssim eq) (at level 70).
Infix "(≲p  L )" := (pssim L) (at level 70).

Notation psst L := (` (_ : Chain (pss L))).
Notation pssbt L := (pssim L (` (_ : Chain (pss L)))).

Infix "[≲p  L ]" := (pss L _) (at level 70).
Infix "[≲p]" := (pss eq _) (at level 70).
Infix "{≲p  L }" := (psst L _) (at level 70).
Infix "{≲p}" := (psst eq _) (at level 70).
Infix "{{≲p  L }}" := (pssbt L _) (at level 70).
Infix "{{≲p}}" := (pssbt eq _) (at level 70).

Notation "[ R ; l ; p | ?→  t ∥ u  →→]" := (pssim_cond R t l p u).

End PSSimNotations.



Section pssim_proper.
Import Enum.
Import EquNotations.
Import GRing.Theory Order.Theory.
Import NonnegQNotations.
#[local] Notation ptree E := (ptree E Enum).


Definition pssim_equb {E F : Type → Type}
{X Y : Type} {L : rel (@label E) (@label F)}
(pssim_equb_: ∀ (x : ptree E X) (a b: ptree F Y), a ≅ b -> x (≲p L) a -> x (≲p L) b)
: ∀ (x : ptree E X) (a b: ptree F Y), a ≅ b -> x (≲p L) a -> x (≲p L) b.
Proof.
  move => x a b equ_eq Hsim. step in Hsim. apply (gfp_fp (pss L)). move => l p x1' Htrans.
  use pssim with Hsim Htrans. exists l'. split. exact: RL.
  inversion HsimCond.
  - step equ in equ_eq. rewrite -H in equ_eq. inversion equ_eq; subst.
    econstructor; eauto.
  - step equ in equ_eq. rewrite -H in equ_eq. inversion equ_eq; subst.
    econstructor; eauto. have t_eq : (Tau t) ≅ (Tau t2). rewrite equ_TauF //=.
    rewrite -transR_trans -(trans_equ l' p (Tau t) (Tau t2) t_eq). exact: H0. rewrite //=.
  - step equ in equ_eq. rewrite -H in equ_eq. dependent destruction equ_eq; subst.
    rewrite -x. econstructor; eauto.
    assert (Vis e k ≅ Vis e k2). step. constructor. intros.
    rewrite REL. reflexivity. rewrite -H2. auto.
  - step equ in equ_eq. rewrite -H in equ_eq. dependent destruction equ_eq; subst.
    rewrite /disc_RT enumRT_eq in REL.
    rewrite -x.
    have s_subset : {subset s  <= supp μ2}.
        move => i in_s. rewrite -(supp_enum_eq_mem_eq REL) (H1 i in_s) //=.
    econstructor; eauto.
    + case: (transAll_Prob_tau μ k H2) => [Hsnil|Htau]. 
      * have size_eq : size ([::] : seq (ℚ≥0 * (ptree F Y))) = size ([::] : seq (ℚ≥0 * (ptree F Y))).
        reflexivity. rewrite -{1}Hsnil //= size_map in size_eq. rewrite (size0nil size_eq) //=.
      * rewrite Htau. apply (transAll_subset_map s_subset). apply transAll_Prob.
    + clear - pssim_equb_ RELk H3. elim : s H3 => [//=|a s IH H3]. rewrite map_cons in H3.
      move : H3 => [H3 H4]. move : IH => /(_ H4) IH.
      rewrite map_cons. split. clear H4 IH s. move : RELk => /(_ a) RELk. rewrite -/(pssim L).
      eapply pssim_equb_. exact: RELk. exact: H3. exact: IH.
    + apply (le_trans H4).
      rewrite -(mass_eq1_of_enumeq REL) //=.
Qed.

(* Program Definition pssim_equ {E F : Type → Type}
{X Y : Type} {L : rel (@label E) (@label F)}
: mon (∀ (x : ptree E X) (a b: ptree F Y), a ≅ b -> x (≲p L) a -> x (≲p L) b)
  := {| body := @pssim_equb E F X Y L |}.
Next Obligation.
Qed. *)

#[global]
Instance pssim_equ_equ {E F : Type → Type}
    {X Y : Type} (L : rel (@label E) (@label F))
  : Proper (equ (R1 := X) eq ==> equ (R1 := Y) eq ==> flip impl)
    (pssim L).
Proof. simpl. intros x1 x2 EQx y1 y2 EQy Hpssim2.
  step in Hpssim2. apply (gfp_fp (pss L)).
  intros l p x1' Htrans. rewrite EQx in Htrans.
  use pssim with Hpssim2 Htrans.
  exists l'; split; auto.
  inversion Hpssim2Cond; subst.
  - step equ in EQy. rewrite -H in EQy. inversion EQy; subst.
    econstructor; eauto.
  - step equ in EQy. rewrite -H in EQy. inversion EQy; subst.
    econstructor; eauto. rewrite REL. auto.
  - step equ in EQy. rewrite -H in EQy. dependent destruction EQy; subst.
    rewrite -x. econstructor; eauto.
    assert (Vis e k ≅ Vis e k1). step. constructor. intros.
    rewrite REL. reflexivity. rewrite -H2. auto.
  - step equ in EQy. rewrite -H in EQy. dependent destruction EQy; subst.
    rewrite /disc_RT enumRT_eq in REL.
    rewrite -x.
    case: (transAll_Prob_tau μ k H2) => [Hsnil|Htau].
    * econstructor. have uniq_nil : uniq [::]. rewrite //=. apply uniq_nil.
      all: rewrite //. rewrite /mass //=.
      have size_eq : size ([::] : seq (ℚ≥0 * (ptree F Y))) = size ([::] : seq (ℚ≥0 * (ptree F Y))).
        reflexivity. rewrite -{1}Hsnil //= size_map in size_eq. have s_nil := size0nil size_eq.
      rewrite s_nil //= in H4.
    * rewrite Htau.
      have s_subset : {subset s  <= supp μ1}.
        move => i in_s. rewrite (supp_enum_eq_mem_eq REL) (H1 i in_s) //=.
      econstructor. exact: H0. exact: s_subset.
      + apply (transAll_subset_map s_subset). apply transAll_Prob.
      + clear - H3 RELk. elim : s H3 => [//=|a s IH H3]. rewrite map_cons in H3. move : H3 => [H3 H4]. move : IH => /(_ H4) IH.
        rewrite map_cons. split. clear H4 IH s. move : RELk => /(_ a) RELk. rewrite -/(pssim L).
        admit. exact: IH.
      + apply (le_trans H4).
        rewrite -(mass_eq1_of_enumeq REL) //=.
Admitted.

End pssim_proper.



Section homogenous_pssim_theory.
Import Enum.
Import GRing.Theory Order.Theory.
Import NonnegQNotations.
Import EquNotations.
Import EquAxioms.
#[local] Notation ptree E := (ptree E Enum).

Context {E : Type → Type} {X : Type}.
Context {L : relation (@label E)}.

#[global]
Instance Reflexive_pss {RC : relation (ptree E X)}
    `{Reflexive _ L} `{Reflexive _ RC}
  : Reflexive (pss L RC).
Proof. unfold Reflexive.
  intros t l p t' Htrans. inversion Htrans; subst.
  - exists (val r); split; auto. inversion Htrans.
    econstructor. rewrite H4. apply Htrans. auto.
  - exists tau; split; auto. econstructor.
    rewrite H1. apply Htrans. auto.
  - exists (obs e x); split; auto. econstructor.
    rewrite H1. apply Htrans. auto.
  - exists tau; split; auto.
    remember (x \in supp μ) as Hmem. destruct Hmem.
    + apply (PSSimProbF _ _ _ _ _ _ _ [:: x]). by [].
      move => m hm. rewrite mem_seq1 in hm.
      rewrite (eqP hm) -HeqHmem //.
      simpl; split; auto. rewrite H1 H6.
      rewrite (ptree_eta t0). rewrite H2. apply Htrans.
      simpl; split; auto.
      (* use axiom [equ_is_eq] here *)
      rewrite (equ_is_eq (ptree_eta t')) -H2
        -(equ_is_eq (ptree_eta t0)) (equ_is_eq H6) //.
      simpl. unfold mass. simpl. rewrite addr0 //.
    + apply (PSSimProbF _ _ _ _ _ _ _ [::]).
      by []. by []. all: simpl; auto.
      unfold mass. simpl. symmetry in HeqHmem.
      rewrite -common.negb_spec notin_supp_iff_acc_mass_eq_0 in HeqHmem.
      rewrite HeqHmem //=.
Qed.

#[global]
Instance Transitive_pss {RC : relation (ptree E X)}
    `{Transitive _ L} `{Transitive _ RC}
  : Transitive (pss L RC).
Proof. unfold Transitive.
  intros s t u Hst Htu. intros l p t' Htrans.
  __use_pssim Hst Htrans. inversion HstCond; subst.
  - inversion H2; subst. rewrite <- H1 in HstCond.
    exists (val r); split; auto.
    Fail rewrite <- H1 in Htu.
Admitted.

#[global]
Instance Reflexive_hpssim `{Reflexive _ L} (RC : Chain (@pss E E X X L))
  : Reflexive (` RC).
Proof. revert RC. apply Reflexive_chain.
  intros RC HRC x. apply Reflexive_pss.
Qed.

#[global]
Instance Transitive_hpssim `{Transitive _ L} (RC : Chain (@pss E E X X L))
  : Transitive (` RC).
Proof. revert RC. apply Transitive_chain.
  intros RC HRC x. apply Transitive_pss.
Qed.

End homogenous_pssim_theory.
