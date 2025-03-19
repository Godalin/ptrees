(** Syntactic Equality over PTrees.
  [eq]: too strong to be usable with coinductive structures
  [equ]: syntactic equality over PTrees, exact the same shape,
    except for the monadic representation of inference problems,
    i.e., the type constructor [M] in [ptree E M R].

    Here, we require a implement of the [DiscreteInterface M],
    which should provide a relation transformer [disc_RT].
  *)

Require Import Morphisms.
Require Import Program.
Require Import EquivDec.

From ExtLib Require Import Monads.

From Coinduction Require Import all.

From PTree.Core Require Import PTreeDefinitionPa Utils.
From PTree.Prob Require Import Discrete.
From PTree.Eq Require Import Shallow.



(** The structural equivalence of [ptree]s.
    This relation should be provided as a typeclass. *)
Section equ.
Context {E M : Type -> Type}.
Context `{DiscreteInterface M}.
Context {R1 R2 : Type}.
Context (RR : R1 -> R2 -> Prop).
Local Notation RM := (disc_RT eq).

Variant equb (eq_ : ptree E M R1 -> ptree E M R2 -> Prop)
    : ptree' E M R1 -> ptree' E M R2 -> Prop :=
  | Eq_Ret x y (REL : RR x y)
      : equb eq_ (RetF x) (RetF y)
  | Eq_Tau t1 t2 (REL : eq_ t1 t2)
      : equb eq_ (TauF t1) (TauF t2)
  | Eq_Vis {X} (e : E X) k1 k2 (REL : forall x, eq_ (k1 x) (k2 x))
      : equb eq_ (VisF e k1) (VisF e k2)
  | Eq_Prob {X} `{EqDec X eq} {μ1 μ2 : M X} k1 k2
        (REL : RM μ1 μ2) (RELk : forall x, eq_ (k1 x) (k2 x))
      : equb eq_ (ProbF μ1 k1) (ProbF μ2 k2).

Hint Constructors equb : core.

(** [equb_] is a monotone function of relations on [ptree E M R] *)
Definition equb_ eq_ : ptree E M R1 -> ptree E M R2 -> Prop
  := fun t1 t2 => equb eq_ (observe t1) (observe t2).

Program Definition fequ : mon (ptree E M R1 -> ptree E M R2 -> Prop)
  := {| body := equb_ |}.
Next Obligation.
  unfold pointwise_relation, impl, equb_.
  intros ?? INC ?? EQ. inversion_clear EQ; eauto.
Qed.

End equ.



(** [equ] is the [gfp] of [fequ] *)

Definition equ {E M} `{DiscreteInterface M} {R1 R2} R
  := gfp (@fequ E M _ R1 R2 R).

#[global] Hint Unfold equ : core.
#[global] Hint Constructors equb : core.
Arguments equb_ {_ _ _ _ _} _/.



(* Ltac fold_equ := *)
(*   repeat *)
(*     match goal with *)
(*     | h : context [@fequ ?E ?M ?DI ?R1 ?R2 ?RR] |- _ => *)
(*       fold (@equ E M DI R1 R2 RR) in h *)
(*     | |- context [@fequ ?E ?M ?DI ?R1 ?R2 ?RR] => *)
(*       fold (@equ E M DI R1 R2 RR) *)
(*     end. *)

(* Ltac __coinduction_equ R H := *)
(*   red; coinduction R H; fold_equ. *)

(* Tactic Notation "__step_equ" := *)
(*   match goal with *)
(*   | |- context [@equ ?E ?M ?DM ?R1 ?R2 ?RR _ _] => *)
(*       unfold equ; step; fold (@equ E M R1 R2 RR); *)
(*       simpl body *)
(*   | |- _ => step *)
(*   end. *)

Ltac __step_equ := step.

#[local] Tactic Notation "step" := __step_equ.

Ltac __step_in_equ H :=
  match type of H with
  | context [@equ ?E ?M ?DM ?R1 ?R2 ?RR _ _] =>
      unfold equ in H; apply (gfp_pfp (fequ RR)) in H;
      fold (@equ E M _ R1 R2 RR) in H; cbn in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_equ H.



(** Useful relation notations *)
Module EquNotations.
Notation "` R" := (elem R) (at level 10).

Infix "≅"      := (equ eq) (at level 70).
Infix "(≅ Q )" := (equ Q) (at level 70).

Notation et Q  := (` (_ : Chain (fequ Q))).
Notation ebt Q := (equb Q (` (_ : Chain (fequ Q)))).

Infix "[≅ Q ]"   := (et Q) (at level 70).
Infix "{≅ Q }"   := (ebt Q) (at level 70).
Infix "{{≅ Q }}" := (equb Q (equ Q)) (at level 70).
Infix "[≅]"   := (et eq) (at level 70).
Infix "{≅}"   := (ebt eq) (at level 70).
Infix "{{≅}}" := (equb eq (equ eq)) (at level 70).
End EquNotations.

Import EquNotations.

Section equ_theory.
Context {E M : Type -> Type} {R : Type}.
Context `{DiscreteInterface M}.
Context {RR : R -> R -> Prop}.

(** [equb] is an [Equivalence] instance transformer *)

#[global] Instance Reflexive_equb {RC} {RRR : Reflexive RR} {RRC : Reflexive RC}
  : Reflexive (@equb E M _ _ _ RR RC).
Proof. unfold Reflexive. intros. destruct x; econstructor; eauto. Qed.

#[global] Instance Symmetric_equb {RC} {SRR : Symmetric RR} {SRC : Symmetric RC}
  : Symmetric (@equb E M _ _ _ RR RC).
Proof. unfold Symmetric. intros x y Hxy. dependent destruction Hxy; econstructor; auto.
  symmetry. assumption.
Qed.

#[global] Instance Transitive_equb {RC} {RRR : Transitive RR} {RRC : Transitive RC}
  : Transitive (@equb E M _ _ _ RR RC).
Proof. unfold Transitive. intros x y z Hxy Hyz.
  dependent destruction Hxy; dependent destruction Hyz; econstructor; eauto.
  transitivity μ2; assumption.
Qed.

#[global] Instance Equivalence_equb {RC} {ERR : Equivalence RR} {ERC : Equivalence RC}
  : Equivalence (@equb E M _ _ _ RR RC).
Proof. split. apply Reflexive_equb. apply Symmetric_equb. apply Transitive_equb. Qed.

(** [equ] makes [Equivalence] [Chain] instances from
    [Equivalence] relations *)

#[global] Instance Equivalence_equ {ERR : Equivalence RR}
    (RC : Chain (@fequ E M _ _ _ RR))
  : Equivalence (` RC).
Proof. split; revert RC.
  - apply Reflexive_chain. intros RC HRC x. apply Reflexive_equb.
  - apply Symmetric_chain. intros RC HRC x y Hxy. apply Symmetric_equb. assumption.
  - apply Transitive_chain. intros RC HRC x y z Hxy Hyz. eapply Transitive_equb.
    apply Hxy. auto.
Qed.



#[global] Instance equb_eq_equ' {X Y} {Q : rel X Y}
    : Proper (equ eq ==> equ eq ==> flip impl) (@equ E M _ _ _ Q).
Proof. unfold Proper, respectful, flip, impl.
  red. coinduction RC IH. intros t t' EQt u u' EQu EQ.
  step in EQt. step in EQu. step in EQ. cbn in *.
  inversion EQt; subst.
  - rewrite <- H2 in EQ. inversion EQ; subst.
    rewrite <- H4 in EQu. inversion EQu; subst.
    now constructor.
  - rewrite <- H2 in EQ. inversion EQ; subst.
    rewrite <- H4 in EQu. inversion EQu; subst.
    constructor. eapply IH; eauto.
  - rewrite <- H2 in EQ. dependent destruction EQ.
    rewrite <- x in EQu. dependent destruction EQu. rewrite <- x.
    constructor. intros xx. eapply IH. apply REL1. apply REL. apply REL0.
  - rewrite <- H3 in EQ. dependent destruction EQ.
    rewrite <- x in EQu. dependent destruction EQu. rewrite <- x.
    econstructor. rewrite REL. rewrite REL1. assumption.
    eauto.
Qed.

#[global] Instance equb_eq_equ {X} {Q : relation X}
    : Proper (equ eq ==> equ eq ==> flip impl) (@equ E M _ _ _ Q).
Proof. apply equb_eq_equ'. Qed.

End equ_theory.



(** Dependent inversion of [equ] and [equb] *)
Section inv.
Context {E M : Type -> Type}.
Context `{DM : DiscreteInterface M}.

(* for [equ] *)

Lemma equ_ret_inv {R} : forall r1 r2 : R,
    (Ret r1 : ptree E M R) ≅ Ret r2 -> r1 = r2.
Proof. intros ?? EQ. step in EQ. now inversion EQ. Qed.

Lemma equ_vis_invT {X Y S} (e1 : E X) (e2 : E Y)
    (k1 : X -> ptree E M S) k2 : Vis e1 k1 ≅ Vis e2 k2 -> X = Y.
Proof. intros EQ. step in EQ. now inversion EQ. Qed.

Lemma equ_vis_invE {X S} (e1 e2 : E X) (k1 k2 : X -> ptree E M S) :
  Vis e1 k1 ≅ Vis e2 k2 ->
  e1 = e2 /\ forall x, k1 x ≅ k2 x.
Proof.
  intros EQ. step in EQ. dependent destruction EQ. auto.
Qed.

Lemma equ_prob_invT {X Y} `{EqDec X eq} `{EqDec Y eq} {S}
    (μ1 : M X) (μ2 : M Y) (k1 : X -> ptree E M S) (k2 : Y -> ptree E M S)
  : Prob μ1 k1 ≅ Prob μ2 k2 -> X = Y.
Proof.
  intros EQ; step in EQ.
	now inversion EQ.
Qed.

Lemma equ_prob_invE {X} `{EqDec X eq} {S}
    (μ1 μ2 : M X) (k1 k2 : X -> ptree E M S)
  : Prob μ1 k1 ≅ Prob μ2 k2 -> disc_eq μ1 μ2 /\ forall x, k1 x ≅ k2 x.
Proof.
  intros EQ. step in EQ. dependent destruction EQ.
  split. apply disc_RTeq. assumption.
  apply RELk.
Qed.

(* for [equb] *)

Lemma equb_vis_invT {X Y S} (e1 : E X) (e2 : E Y)
    (k1 : X -> ptree E M S) k2
  : equb eq (equ eq) (VisF e1 k1) (VisF e2 k2) -> X = Y.
Proof. intros EQ. now dependent destruction EQ. Qed.

Lemma equb_vis_invE {X S} (e1 e2 : E X) (k1 k2 : X -> ptree E M S)
  : equb eq (equ eq) (VisF e1 k1) (VisF e2 k2) ->
    e1 = e2 /\ forall x, equ eq (k1 x) (k2 x).
Proof.
  intros EQ. inversion EQ.
  dependent destruction H; dependent destruction H4; auto.
Qed.

Lemma equb_prob_invT {X Y} `{EqDec X eq} `{EqDec Y eq} {S}
    (μ1 : M X) (μ2 : M Y)
    (k1 : X -> ptree E M S) (k2 : Y -> ptree E M S)
  : equb eq (equ eq) (ProbF μ1 k1) (ProbF μ2 k2) -> X = Y.
Proof.
  intros EQ.
	dependent induction EQ; auto.
Qed.

Lemma equb_prob_invE {X} `{EqDec X eq} {S} (μ1 μ2 : M X)
    (k1 : _ -> ptree E M S) k2
  : equb eq (equ eq) (ProbF μ1 k1) (ProbF μ2 k2) ->
    disc_eq μ1 μ2 /\ forall x, k1 x ≅ k2 x.
Proof.
  intros EQ. dependent destruction EQ.
  split; auto. now rewrite disc_RTeq.
Qed.

End inv.



(** [Proper] instances *)
Section proper.
Context {E M : Type -> Type} {R : Type}.
Context `{DM : DiscreteInterface M}.

(** coinductive structural equality
    maybe above are also included *)

#[global] Instance equ_observe
  : Proper (equ eq ==> going (equ eq)) (@observe E M R).
Proof. constructor. step in H. now step. Qed.

#[global] Instance equ_ProbF {X} `{EqDec X eq}
  : Proper (disc_RT eq ==> pointwise_relation _ (equ eq) ==> going (equ eq))
    (@ProbF E M R _ _ _ _).
Proof. constructor. red in H1. step. econstructor; eauto. Qed.

#[global] Instance equ_VisF {X} (e : E X)
  : Proper (pointwise_relation _ (equ eq) ==> going (equ eq))
    (@VisF E M R _ _ e).
Proof. constructor. red in H. step. econstructor; eauto. Qed.

#[global] Instance equ_TauF
  : Proper (equ eq ==> going (equ eq))
    (@TauF E M R _).
Proof. constructor. red in H. step. econstructor; eauto. Qed.



#[global] Instance observing_sub_equ
  : subrelation (@observing E M R R eq) (equ eq).
Proof. repeat intro.
  step. rewrite (observing_observe H). apply Reflexive_equb; eauto.
Qed.

#[global] Instance equ_eq_equ {RC : Chain (@fequ E M _ R R eq)}
  : Proper (going (equ eq) ==> eq ==> flip impl)
	  (@equb E M _ R R eq (` RC)).
Proof.
  unfold Proper, respectful, flip, impl. intros. subst.
  inversion H. step in H0. inversion H0; subst; auto.
  inversion H1; subst. constructor. rewrite REL. auto.
  dependent destruction H1. econstructor. intros. rewrite REL0. auto.
  dependent destruction H1. econstructor. transitivity μ2; auto.
  intros. rewrite RELk0. auto.
Qed.

#[global] Instance eq_equ_equ {RC : Chain (@fequ E M _ R R eq)}
  : Proper (eq ==> going (equ eq) ==> flip impl)
	   (@equb E M _ R R eq (` RC)).
Proof.
  unfold Proper, respectful, flip, impl. intros. subst.
  inversion H0; subst. step in H.
  inversion H; subst; inversion H1; subst. auto.
  - econstructor. now rewrite REL.
  - dependent destruction H5. dependent destruction H6.
    econstructor. intros. now rewrite REL.
  - dependent destruction H9; subst. dependent destruction H10.
    econstructor; eauto. rewrite REL0. now symmetry.
    intro. rewrite RELk0. symmetry. rewrite RELk. reflexivity.
Qed.

#[global] Instance equ_equ_equ {RC : Chain (@fequ E M _ R R eq)}
  : Proper (going (equ eq) ==> going (equ eq) ==> flip impl)
	   (@equb E M _ R R eq (` RC)).
Proof.
  unfold Proper, respectful, flip, impl. intros.
  inversion H; subst. step in H2.
  inversion H0; subst. step in H3.
  inversion H2; subst; inversion H3; subst; eauto.
  all: try now inversion H1.
  - inversion H1; subst. econstructor. rewrite REL, REL0; assumption.
  - dependent destruction H1. econstructor.
    intro x. rewrite REL0, REL1. apply REL.
  - dependent destruction H1. econstructor.
    rewrite REL0, REL1. assumption.
    intro x. rewrite RELk0, RELk1. apply RELk.
Qed.

Lemma observe_equ_eq
  : forall (t u: ptree E M R),
    observe t = observe u -> t ≅ u.
Proof. intros. step. rewrite H. reflexivity. Qed.

End proper.



(** * Up-To [bind] Reasoning *)
(** Given [t ≅ u], how to show that [t >>= k] and [u >>= h] are bisimilar?
    The goal is to show that, the function
    [ f R = {(bind t k, bind u h) | equ SS t u ∧ ∀ x y, SS x y → R (k x) (h y)} ]
    is a valid enhancement.
  *)

Section bind.

Definition pointwise {X X' Y Y'} (SS : rel X X')
    : rel Y Y' -> rel (X -> Y) (X' -> Y') :=
  fun R k k' => forall x x', SS x x' -> R (k x) (k' x').

Definition pairH {A B : Type} (x : A) (y : B) : rel A B :=
  fun x' y' => x = x' /\ y = y'.

Lemma leq_pairH : forall A B (x : A) (y : B) (R : rel A B),
    R x y <-> pairH x y <= R.
Proof. firstorder congruence. Qed.



Section bind_ctx.

Context {E F M N : Type -> Type}.
Context `{DiscreteInterface M}.
Context `{DiscreteInterface N}.

Definition bind_ctx {X X' Y Y'}
    (R : rel (ptree E M X) (ptree F N X'))
    (S : rel (X -> ptree E M Y) (X' -> ptree F N Y'))
  : rel (ptree E M Y) (ptree F N Y') :=
  fun t t' =>
  exists x, exists x', R x x' /\ exists k, exists k', S k k' /\
    pairH (bind x k) (bind x' k') t t'.

Lemma leq_bind_ctx {X X' Y Y'}
    (R : rel (ptree E M X) (ptree F N X'))
    (S : rel (X -> ptree E M Y) (X' -> ptree F N Y'))
    (S' : rel (ptree E M Y) (ptree F N Y'))
  : bind_ctx R S <= S' <-> (forall x x', R x x' -> forall k k',
      S k k' -> S' (bind x k) (bind x' k')).
Proof. split.
  - intros. apply H1. unfold bind_ctx.
    repeat (repeat econstructor; eauto).
  - intros. unfold bind_ctx.
    intros t t' [x [x' [HR [k [k' [HS HpairH]]]]]].
    unfold pairH in HpairH. destruct HpairH; subst.
    apply H1; auto.
Qed.

Lemma in_bind_ctx {X X' Y Y'}
    (R : rel (ptree E M X) (ptree F N X'))
    (S : rel (X -> ptree E M Y) (X' -> ptree F N Y')) x x' y y'
  : R x x' -> S y y' -> bind_ctx R S (bind x y) (bind x' y').
Proof. intros. apply (leq_bind_ctx R S).
  - intros. repeat econstructor; auto.
  - unfold bind_ctx. repeat econstructor; auto.
Qed.

#[global] Opaque bind_ctx.

End bind_ctx.



Section equ_bind_ctx.

Context {E M : Type -> Type}.
Context `{DiscreteInterface M}.
Context {X1 X2 Y1 Y2 : Type}.

(* An enhancement function.
  [bind_ctx_equ SS] is a monotone function on
  [rel (ptree E M R1) (ptree E M R2)]. It contains pairs
  [(t1, t2)] where there exists [x1 (≅SS) x2], [k1 (pointwise SS R) k2]
    s.t. [t1 = bind x1 k1] and [t2 = bind x2 k2], and resulting that.
  [(bind x1 k1, bind x2 k2) ∈ R].
  *)
Program Definition bind_ctx_equ (SS : rel X1 X2)
  : mon (rel (ptree E M Y1) (ptree E M Y2))
  := {| body := fun R =>
    @bind_ctx E E M M X1 X2 Y1 Y2 (equ SS) (pointwise SS R) |}.
Next Obligation.
  repeat red. intros. revert H1. apply leq_bind_ctx.
  intros. apply in_bind_ctx; auto. repeat intro. apply H0. auto.
Qed.

(* The "up-to" technique given by the resulting enhancement function.
  The type of original version in the code of [CTree] is:
  [bind_ctx SS <= et RR], in the words of tower induction, that is,
  [bind_ctx SS (` RC) <= (` RC)] with a little bit lemma
  *)
Lemma bind_ctx_equ_chain (SS : rel X1 X2) (RR : rel Y1 Y2)
    (RYC : Chain (@fequ E M _ _ _ RR))
  : bind_ctx_equ SS (` RYC) <= (` RYC).
Proof. apply tower.
  2:{ intros RC IH y1 y2 Hb.
      destruct Hb as [x1 [x2 [Hx [k1 [k2 [Hk [? ?]]]]]]].
      subst. cbn. step in Hx.
      inversion Hx; repeat rewrite observe_bind.
      - rewrite <- H1. rewrite <- H2.
        apply Hk in REL. cbn in REL. auto.
      - rewrite <- H1. rewrite <- H2. econstructor.
        apply IH. cbn. repeat econstructor; auto.
        intros x11 x22. intros HS12. apply (b_chain RC).
        apply Hk. auto.
      - rewrite <- H1. rewrite <- H2. econstructor.
        intro x. apply IH. cbn. repeat econstructor; auto.
        intros x11 x22. intros HS12. apply (b_chain RC).
        apply Hk. auto.
      - rewrite <- H2. rewrite <- H3. econstructor; auto.
        intro x. apply IH. cbn. repeat econstructor; auto.
        intros x11 x22. intros HS12. apply (b_chain RC).
        apply Hk. auto.
    }
  - red. intros. intros a b Hab. intros P TP.
    cbn in H0. pose proof (HH := H0 P TP a b).
    destruct Hab as [x1 [x2 [Hx [k1 [k2 [Hk [Heq1 Heq2]]]]]]].
    apply HH. repeat econstructor; eauto.
    intros x11 x22 HS. apply Hk; auto.
Qed.

End equ_bind_ctx.
End bind.

(** Reasoning Rules Provided by Up-To principle. *)

Section rules.
Context {E M : Type -> Type}.
Context `{DiscreteInterface M}.

Lemma clo_bind_chain {X1 X2 Y1 Y2} :
  forall {t1 : ptree E M X1} {t2 : ptree E M X2}
    {k1 : X1 -> ptree E M Y1} {k2 : X2 -> ptree E M Y2}
    (S : rel X1 X2) (R : rel Y1 Y2) (RYC : Chain (@fequ E M _ _ _ R)),
      equ S t1 t2 ->
      (forall x1 x2, S x1 x2 -> (` RYC) (k1 x1) (k2 x2)) ->
      (` RYC) (bind t1 k1) (bind t2 k2).
Proof. intros. apply (bind_ctx_equ_chain S R).
  now apply in_bind_ctx.
Qed.

Lemma clo_bind_eq_chain {X Y1 Y2} :
  forall {t : ptree E M X} {k1 : X -> ptree E M Y1} {k2 : X -> ptree E M Y2}
    (R : rel Y1 Y2) (RYC : Chain (@fequ E M _ _ _ R)),
      (forall x, (` RYC) (k1 x) (k2 x)) -> (` RYC) (bind t k1) (bind t k2).
Proof. intros. apply (clo_bind_chain eq).
  reflexivity. intros; subst. auto.
Qed.

#[global] Instance bind_equ_cong_chain {X Y} (R : relation Y)
    (RYC : Chain (@fequ E M _ _ _ R))
  : Proper (equ (@eq X) ==> pointwise_relation X (` RYC) ==> ` RYC)
    bind.
Proof. red. red. red. intros t u Hx k1 k2 Hk.
  eapply clo_bind_chain; eauto.
  intros ?? <-. auto.
Qed.

#[global] Instance bind_equ_cong {X Y}
  : Proper (@equ E M _ _ _ eq ==>
      pointwise_relation X (equ (@eq Y)) ==> (equ (@eq Y)))
    bind.
Proof. apply bind_equ_cong_chain. Qed.


(* #[global] Instance bind_chain {X Y} (S : relation X) (R : relation Y) *)
(*     (RXC : Chain (@fequ E M _ _ _ S)) *)
(*     (RYC : Chain (@fequ E M _ _ _ R)) *)
(*   : Proper (` RXC ==> pointwise_relation X (` RYC) ==> ` RYC) *)
(*     bind. (* @bind (ptree E M) _ X Y. *) *)
(* Proof. red. red. red. intros t u Hx k1 k2 Hk. *)
(*   - eapply clo_bind_chain; eauto. *)
(* Qed. *)

End rules.



(*+ Elementary Equational Theory *)

Section equational.
Import PTree.
Import PTreeNotations.
Open Scope ptree.

Context {E M : Type -> Type}.
Context `{DiscreteInterface M}.

(** * η-expensions  *)

Lemma ptree_eta_ {R} (t : ptree E M R) : t ≅ go (_observe t).
Proof. now step. Qed.

Lemma ptree_eta {R} (t : ptree E M R) : t ≅ go (observe t).
Proof. now step. Qed.

Lemma ptree_eta' {R} (ot : ptree' E M R) : ot = observe (go ot).
Proof. reflexivity. Qed.

Import MonadNotation.
Local Open Scope monad_scope.

Notation bind_ t k :=
  match observe t with
  | RetF r => k%function r
  | TauF u => Tau (bind u k)
  | VisF e ke => Vis e (fun x => bind (ke x) k)
  | ProbF μ kμ => Prob μ (fun x => bind (kμ x) k)
  end.

Lemma unfold_bind {R S} (t : ptree E M R) (k : R -> ptree E M S)
  : bind t k ≅ bind_ t k.
Proof. now step. Qed.

Notation iter_ step i :=
  (lr <- step%function i;;
   match lr with
   | inl l => Tau (iter step l)
   | inr r => Ret r
   end)%ptree.

Lemma unfold_iter {R I} (step : I -> ptree E M (I + R)) i:
	iter step i ≅ iter_ step i.
Proof. now step. Qed.

End equational.



(** * Monadic laws *)
Section monadic.
Import PTree.
Import PTreeNotations.
Local Open Scope ptree_scope.
Import MonadNotation.
Local Open Scope monad_scope.

Context {E M : Type -> Type}.
Context `{DiscreteInterface M}.

Lemma bind_ret_l {X Y} : forall (x : X) (k : X -> ptree E M Y),
    (ret x >>= k) ≅ k x.
Proof. intros. cbn. now rewrite unfold_bind. Qed.

Lemma bind_ret_r {X} : forall (t : ptree E M X),
    x <- t ;; ret x ≅ t.        (* bind t ret = t *)
Proof. unfold equ.
  coinduction R CIH.
  intros t. cbn.
  rewrite unfold_bind.
  cbn in *. desobs t Heq; constructor; auto.
Qed.

Lemma bind_bind {X Y Z} : forall (t : ptree E M X)
    (k : X -> ptree E M Y) (h : Y -> ptree E M Z),
    t >>= k >>= h ≅ t >>= (fun x => k x >>= h).
Proof. unfold equ.
  coinduction S CIH. intros.
  cbn. rewrite (ptree_eta t). cbn.
  desobs t; cbn.
  - reflexivity.
  - constructor; intros. apply CIH.
  - constructor; intros. apply CIH.
  - constructor; intros. reflexivity. eapply CIH.
Qed.

End monadic.



(** * Structural rules *)
Section structural.
Context {E M : Type -> Type} {R S : Type}.
Context `{DiscreteInterface M}.
Import PTree.
Import MonadNotation.
Local Open Scope monad_scope.

Lemma bind_vis {X Y Z} (e : E X)
    (k : X -> ptree E M Y) (g : Y -> ptree E M Z)
  : Vis e k >>= g ≅ Vis e (fun x => k x >>= g).
Proof. cbn. now rewrite unfold_bind. Qed.

Lemma bind_trigger {X Y} (e : E X) (k : X -> ptree E M Y)
  : trigger e >>= k ≅ Vis e k.
Proof.
  unfold trigger. rewrite bind_vis. setoid_rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma bind_prob {X Y Z} `{EqDec X eq} (μ : M X)
    (k : X -> ptree E M Y) (g : Y -> ptree E M Z)
  : Prob μ k >>= g ≅ Prob μ (fun x => k x >>= g).
Proof. cbn. now rewrite unfold_bind. Qed.

Lemma bind_tau {X Y} (t : ptree E M X) (g : X -> ptree E M Y)
  : Tau t >>= g ≅ Tau (t >>= g).
Proof. cbn. rewrite unfold_bind. now cbn. Qed.

Lemma vis_equ_bind {X Y Z}
  : forall (t : ptree E M X) (e : E Z) k (k' : X -> ptree E M Y),
      x <- t;; k' x ≅ Vis e k ->
      (exists r, t ≅ Ret r) \/
      exists k0, t ≅ Vis e k0 /\ forall x, k x ≅ x <- k0 x;; k' x.
Proof.
  intros.
  destruct (observe t) eqn:?.
  - left. exists r. now rewrite ptree_eta, Heqp.
  - rewrite (ptree_eta t), Heqp, bind_tau in H0.
    step in H0. inversion H0.
  - rewrite (ptree_eta t), Heqp, bind_vis in H0.
    apply equ_vis_invT in H0 as ?; subst.
    apply equ_vis_invE in H0 as ?; destruct H1; subst.
    right. exists k0. split.
    2:{ intro. symmetry. apply H2. }
    + rewrite (ptree_eta t). now rewrite <- Heqp.
  - rewrite (ptree_eta t), Heqp, bind_prob in H0.
    step in H0. inversion H0.
Qed.

Lemma ret_equ_bind {X Y}
  : forall (t : ptree E M Y) (k : Y -> ptree E M X) r,
    x <- t;; k x ≅ ret r ->
    exists r1, t ≅ ret r1 /\ k r1 ≅ ret r.
Proof.
  intros. rewrite (ptree_eta t) in H0. (* rewrite (ptree_eta t). *)
  destruct (observe t) eqn:?.
  - rewrite (bind_ret_l r0 k) in H0. econstructor; split.
    unfold ret. rewrite <- Heqp. rewrite <- (ptree_eta t).
    all: auto.
  - rewrite bind_tau in H0. step in H0. inversion H0.
  - rewrite bind_vis in H0. step in H0. inversion H0.
  - rewrite bind_prob in H0. step in H0. inversion H0.
Qed.

Lemma prob_equ_bind {X Y Z} `{EqDec Z eq}
  : forall (t : ptree E M X) (μ : M Z) k (k' : X -> ptree E M Y),
    x <- t;; k' x ≅ Prob μ k ->
    (exists r, t ≅ Ret r) \/
    exists k0, t ≅ Prob μ k0 /\ forall x, k x ≅ x <- k0 x;; k' x.
Proof.
  intros.
  destruct (observe t) eqn:?.
  - left. exists r. rewrite ptree_eta, Heqp. reflexivity.
  - rewrite (ptree_eta t), Heqp, bind_tau in H1. step in H1. inversion H1.
  - rewrite (ptree_eta t), Heqp, bind_vis in H1. step in H1. inversion H1.
  - rewrite (ptree_eta t), Heqp, bind_prob in H1.
    apply equ_prob_invT in H1 as ?. subst.
    step in H1. dependent destruction H1.
    right. exists k0. split.
    + rewrite (ptree_eta t). rewrite Heqp.
      rewrite REL. reflexivity.
    + intro z. cbn. now rewrite RELk.
Qed.



(** *map laws *)

(* TODO *)

End structural.
