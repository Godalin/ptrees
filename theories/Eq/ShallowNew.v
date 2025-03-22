(** * Shallow equivalence
    This file comes from the [ITree] library *)

(** Equality under [observe]:

[[
  observing eq t1 t2 <-> t1.(observe) = t2.(observe)
]]

  We actually define a more general *relation transformer*
  [observing] to lift arbitrary relations through [observe].

*)

(* begin hide *)
Require Import Morphisms.

From PTree.Core Require Import PTreeDefinitionNew.

Set Implicit Arguments.
(* end hide *)

Definition eqeq {A : Type} (P : A -> Type) {a1 a2 : A} (p : a1 = a2) : P a1 -> P a2 -> Prop :=
  match p with
  | eq_refl => eq
  end.

Definition pweqeq {R1 R2} (RR : R1 -> R2 -> Prop) {X1 X2 : Type} (p : X1 = X2)
  : (X1 -> R1) -> (X2 -> R2) -> Prop :=
  match p with
  | eq_refl => fun k1 k2 => forall x, RR (k1 x) (k2 x)
  end.

Lemma pweqeq_mon {R1 R2} (RR1 RR2 : R1 -> R2 -> Prop) X1 X2 (p : X1 = X2) k1 k2
  : (forall r1 r2, RR1 r1 r2 -> RR2 r1 r2) -> pweqeq RR1 p k1 k2 -> pweqeq RR2 p k1 k2.
Proof.
  destruct p; cbn; auto.
Qed.

Lemma eq_inv_VisF_weak {E M R X1 X2} (e1 : E X1) (e2 : E X2)
    (k1 : X1 -> ptree E M R) (k2 : X2 -> ptree E M R)
  : VisF (R := R) (M := M) e1 k1 = VisF (R := R) e2 k2 ->
    exists p : X1 = X2, eqeq E p e1 e2 /\ eqeq (fun X => X -> ptree E M R) p k1 k2.
Proof.
  refine (fun H =>
    match H in _ = t return
      match t with
      | VisF _ e2 k2 => _
      | _ => True
      end
    with
    | eq_refl => _
    end); cbn.
  exists eq_refl; cbn; auto.
Qed.

Ltac inv_Vis :=
  discriminate +
  match goal with
  | [ E : VisF _ _ = VisF _ _ |- _ ] =>
     apply eq_inv_VisF_weak in E; destruct E as [ <- [<- <-]]
  end.

(** ** [observing]: Lift relations through [observe]. *)
Record observing {E M R1 R2}
           (eq_ : ptree' E M R1 -> ptree' E M R2 -> Prop)
           (t1 : ptree E M R1) (t2 : ptree E M R2) : Prop :=
  observing_intros
  { observing_observe : eq_ (observe t1) (observe t2) }.
#[global] Hint Constructors observing : ptree.



Section observing_relations.

Context {E M : Type -> Type} {R : Type}.
Variable (eq_ : ptree' E M R -> ptree' E M R -> Prop).

#[global]
Instance observing_observe_ :
  Proper (observing eq_ ==> eq_) (@observe E M R).
Proof. intros ? ? []; cbv; auto. Qed.

#[global]
Instance observing_go : Proper (eq_ ==> observing eq_) (@go E M R).
Proof. cbv; auto with ptree. Qed.

#[global]
Instance monotonic_observing eq_' :
  subrelation eq_ eq_' ->
  subrelation (observing eq_) (observing eq_').
Proof. intros ? ? ? []; cbv; eauto with ptree. Qed.

#[global]
Instance Equivalence_observing :
  Equivalence eq_ -> Equivalence (observing eq_).
Proof with (auto with ptree).
  intros []; split; cbv...
  - intros ? ? []; auto...
  - intros ? ? ? [] []; eauto with ptree.
Qed.

End observing_relations.



(** Unfolding lemmas for [bind] *)

Lemma observe_bind {E M R S} (t : ptree E M R) (k : R -> ptree E M S)
  : observe (PTree.bind t k)
  = observe (match observe t with
    | RetF r => k r
    | TauF t0 => Tau (PTree.bind t0 k)
    | VisF _ e ke => Vis e (fun x => PTree.bind (ke x) k)
    | ProbF _ μ k' => Prob μ (fun x => PTree.bind (k' x) k)
    end).
Proof. reflexivity. Qed.

#[global]
Instance observing_bind {E M R S} :
  Proper (observing eq ==> eq ==> observing eq) (@PTree.bind E M R S).
Proof.
  repeat intro; subst. constructor. unfold observe. cbn.
  rewrite (observing_observe H). reflexivity.
Qed.

Lemma bind_ret_ {E M R S} (r : R) (k : R -> ptree E M S) :
  observing eq (PTree.bind (Ret r) k) (k r).
Proof. constructor; reflexivity. Qed.

Lemma bind_tau_ {E M R} U t (k : U -> ptree E M R) :
  observing eq (PTree.bind (Tau t) k) (Tau (PTree.bind t k)).
Proof. constructor; reflexivity. Qed.

Lemma bind_vis_ {E M R U V} (e : E V)
  (ek : V -> ptree E M U) (k : U -> ptree E M R) :
  observing eq
    (PTree.bind (Vis e ek) k)
    (Vis e (fun x => PTree.bind (ek x) k)).
Proof. constructor; reflexivity. Qed.

(** Unfolding lemma for [aloop]. There is also a variant [unfold_aloop]
    without [Tau]. *)
Lemma unfold_aloop_ {E M A B} (f : A -> ptree E M (A + B)) (x : A) :
  observing eq
    (PTree.iter f x)
    (PTree.bind (f x) (fun lr => PTree.on_left lr l (Tau (PTree.iter f l)))).
Proof. constructor; reflexivity. Qed.



(** Unfolding lemma for [forever]. *)
(* Lemma unfold_forever_ {E M R S} (t : ptree E M R):
  observing eq (@PTree.forever E R S t) (PTree.bind t (fun _ => Tau (PTree.forever t))).
Proof. econstructor. reflexivity. Qed. *)



(** [going]: Lift relations through [go]. *)

Inductive going {E M R1 R2}
    (r : ptree E M R1 -> ptree E M R2 -> Prop)
    (ot1 : ptree' E M R1) (ot2 : ptree' E M R2) : Prop :=
  | going_intros : r (go ot1) (go ot2) -> going r ot1 ot2.
#[global] Hint Constructors going : ptree.

Lemma observing_going {E M R1 R2} (eq_ : ptree' E M R1 -> ptree' E M R2 -> Prop) ot1 ot2 :
  going (observing eq_) ot1 ot2 <-> eq_ ot1 ot2.
Proof.
  split; auto with ptree.
  intros [[]]; auto.
Qed.



Section going_relations.

Context {E M : Type -> Type} {R : Type}.
Variable (eq_ : ptree E M R -> ptree E M R -> Prop).

#[global]
Instance going_go : Proper (going eq_ ==> eq_) (@go E M R).
Proof. intros ? ? []; auto. Qed.

#[global]
Instance monotonic_going eq_' :
  subrelation eq_ eq_' ->
  subrelation (going eq_) (going eq_').
Proof. intros ? ? ? []; eauto with ptree. Qed.

#[global]
Instance Equivalence_going :
  Equivalence eq_ -> Equivalence (going eq_).
Proof.
  intros []; constructor; cbv; eauto with ptree.
  - intros ? ? []; auto with ptree.
  - intros ? ? ? [] []; eauto with ptree.
Qed.

End going_relations.
