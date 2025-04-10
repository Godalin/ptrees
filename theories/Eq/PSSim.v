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


Variant pssim_cond : (ptree' F Y) → Enum (label * ptree F Y) → Prop :=
  | PSSimTransF
    : ∀ l' p' u u',
        trans l' p' u u'
      → pssim_cond (observe u) [:: (p', (l', u'))]
  | PSSimProbF
    : ∀ (X' : eqType) (μ : Enum X') (k : X' → ptree F Y) (s : seq X') (kl : X' → @label F),
        uniq s
      → {subset s <= supp μ}
      → transAll (Prob μ k) [seq (acc_mass x μ, (kl x, k x)) | x <- s]
      → pssim_cond (ProbF μ k) [seq (acc_mass x μ, (kl x, k x)) | x <- s].

End experiment.



(** [pss] is the monotone function for probabilistic strong simulation  *)

#[program]
Definition pss {E F : Type → Type}
    {X Y : Type} (L : rel (@label E) (@label F))
  : mon (ptree E X → ptree F Y → Prop)
  := {| body R t u := ∀ l (p : ℚ≥0) t',
        trans l p t t' → ∃ u's : Enum (label * ptree F Y),
            p <= sumq [seq fst i | i <- u's]
          ∧ pssim_cond (observe u) u's
          ∧ relateAll R t' [seq snd (snd i) | i <- u's]
     |}.
Next Obligation.
  move: H0 => /(_ l p t' H1) [u's [p_le_sum [HCond Rall]]].
  exists u's; split; auto. split; auto.
  apply (relateAll_sub x); auto.
Defined.



(** [pssim] is the probabilistic similarity, which is defined as
    the greatest fixpoint of the monotone function [pss] *)

Definition pssim {E F X Y} L := (gfp (@pss E F X Y L)).

End PSSim.



(** pss tactics *)

Ltac __step_pssim :=
  match goal with
  | |- @pssim ?E ?F ?X ?Y ?RL _ _ =>
      unfold pssim; apply (gfp_fp (pss RL))
  | _ => fail "Fail to step pssim in goal"
  end.
#[local] Tactic Notation "step" := __step_pssim || step.

Tactic Notation "step" "pssim" := __step_pssim || step.

Ltac __step_in_pssim H :=
  match type of H with
  | context [@pssim ?E ?F ?X ?Y ?RL] =>
      unfold pssim in H; apply (gfp_pfp (pss RL)) in H;
      fold (@pssim E F X Y RL) in H
  | _ => fail "Fail to step pssim in hypothesis"
  end.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_pssim H.

Tactic Notation "step" "pssim" "in" ident(H) := __step_in_pssim H.

Ltac __use_pssim Hpssim Htrans :=
  apply Hpssim in Htrans;
  let u's := fresh "u's" in
  let Hp_le_sumq := fresh "Hp_le_sumq" in
  let Hpssim_cond := fresh Hpssim "Cond" in
  let HrelAll := fresh "HrelAll_" u's in
  destruct Htrans as [u's [Hp_le_sumq [Hpssim_cond HrelAll]]].
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

Notation "[ R ; p | ?→  t ∥ u  →→]" := (pssim_cond R t p u).

End PSSimNotations.



Section pssim_proper.
Import Enum.
Import EquNotations.
Import GRing.Theory Order.Theory.
Import NonnegQNotations.
#[local] Notation ptree E := (ptree E Enum).

(* #[global] *)
(* Instance pssim_cond_proper {E : Type → Type} {l' : @label E} p {X} *)
(*   : Proper (equb (R1 := X) eq (equ eq) ==> pssim_cond_ l' p). *)

#[global]
Instance pss_equ_equ {E F : Type → Type}
    {X Y : Type} (L : rel (@label E) (@label F))
  : Proper (equ (R1 := X) eq ==> equ (R1 := Y) eq ==> impl)
    (pss L (pssim L)).
Proof. simpl. intros t1 t2 EQt u1 u2 EQu H2 l p t1' HT1.
  rewrite -EQt in HT1. use pssim with H2 HT1. exists u's; split; auto.
  inversion H2Cond; subst. all: step equ in EQu; rewrite -H in EQu; inversion EQu; subst.
  - split. rewrite -H -H3 //= in H2Cond. exact: HrelAll_u's.
  - split. rewrite H4. econstructor. eapply trans_equ_aux2. admit. reflexivity. exact: H0. exact: HrelAll_u's.
(*  - dependent destruction H6; subst. dependent destruction H7; subst.
    assert (Vis e k ≅ Vis e k0). step. constructor. intros x. rewrite REL. reflexivity.
    econstructor. rewrite -H3. apply H0. apply H1.
  - dependent destruction H9; subst. dependent destruction H10; subst.
    econstructor. apply H0. intros i in_s.
    rewrite /disc_RT in REL.
    Fail rewrite -(supp_enum_eq_mem_eq REL). *)
Admitted.

(*
#[global]
Instance pssim_equ_equ {E F : Type → Type}
    {X Y : Type} (L : rel (@label E) (@label F))
  : Proper (equ (R1 := X) eq ==> equ (R1 := Y) eq ==> flip impl)
    (pssim L).
Proof. simpl. unfold pssim at 2. coinduction RC CIH.
  intros x1 x2 EQx y1 y2 EQy Hpssim2.
  step in Hpssim2.
  intros l p x1' Htrans. rewrite EQx in Htrans.
  use pssim with Hpssim2 Htrans.
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
      + clear - H3 RELk CIH. elim : s H3 => [//=|a s IH H3]. rewrite map_cons in H3. move : H3 => [H3 H4]. move : IH => /(_ H4) IH.
        rewrite map_cons. split. clear H4 IH s. move : RELk => /(_ a) RELk. rewrite -/(pssim L).
        eapply CIH. reflexivity. exact: RELk. exact: H3. exact: IH.
      + apply (le_trans H4).
        rewrite -(mass_eq1_of_enumeq REL) //=.
Qed.
*)
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
(*
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
*)

#[global]
Instance Transitive_pss {RC : relation (ptree E X)}
    `{Transitive _ L} `{Transitive _ RC}
  : Transitive (pss L RC).
Proof. unfold Transitive.
  intros s t u Hst Htu. intros l p s' Htrans.
  use pssim with Hst Htrans. inversion HstCond; subst.
  - rewrite (observe_equ_eq _ _ H1) in H2. use pssim with Htu H2. exists u's; split.
    + rewrite //= addr0 in Hp_le_sumq. apply (le_trans Hp_le_sumq). exact: Hp_le_sumq0.
    + split; auto. rewrite //= in HrelAll_u's. eapply relateAll_trans;auto. move: HrelAll_u's => [HrelAll_u's _]. exact : HrelAll_u's. exact: HrelAll_u's0.
  - rewrite transAll_iff_forall_map //= in H4.
    assert (∀ x : X', x \in s0 → transR (kl x) (acc_mass x μ) t (k x)).
    { intros. rewrite transR_trans. rewrite (ptree_eta t) -H1.
      apply H4. auto. }
    (* 这里要把H4中的(Prob μ k)换成t *) rewrite (observe_equ_eq _ _ H1) in H4.
    (* 这里要构造一个把s0每一项都应用于Htu上的列表 *) exists (flatten [seq (Htu (H4 i _)).1 | i <- s]). admit.
Admitted.

#[global]
Instance Reflexive_hpssim `{Reflexive _ L} {RC : Chain (@pss E E X X L)}
  : Reflexive (` RC).
Proof. revert RC. apply Reflexive_chain.
  intros RC HRC x. apply Reflexive_pss.
Qed.

#[global]
Instance Transitive_hpssim `{Transitive _ L} {RC : Chain (@pss E E X X L)}
  : Transitive (` RC).
Proof. revert RC. apply Transitive_chain.
  intros RC HRC x. apply Transitive_pss.
Qed.

#[global]
Instance PreOrder_hpssim `{PreOrder _ L} {RC : Chain (@pss E _ X _ L)}
  : PreOrder (` RC).
Proof. split; typeclasses eauto. Qed.

End homogenous_pssim_theory.



Section heterogenous_pssim_theory.
Import Enum.
Import GRing.Theory Order.Theory.
Import NonnegQNotations.
Import EquNotations.
Import EquAxioms.
#[local] Notation ptree E := (ptree E Enum).


Context {E F : Type → Type} {X Y : Type}.
Context {L : rel (@label E) (@label F)}.

Notation ss := (@pss E F X Y L).
Notation ssim := (@pssim E F X Y L).



End heterogenous_pssim_theory.
