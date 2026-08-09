Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

From mathcomp Require Import ssreflect seq ssralg.

From PTree.Prob Require Import RatSubTypes DiscreteMC.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import RatSubTypes.
Import GRing.Theory.

Lemma bind_Enum_app {A B}
    (mu nu : Enum A) (k : A -> Enum B) :
  bind_Enum (mu ++ nu) k =
  bind_Enum mu k ++ bind_Enum nu k.
Proof.
  elim: mu => [//=|[p a] mu IH] //=.
  by rewrite IH catA.
Qed.

Lemma bind_Enum_scale {A B}
    (p : nnQ) (mu : Enum A) (k : A -> Enum B) :
  bind_Enum (scale_Enum p mu) k =
  scale_Enum p (bind_Enum mu k).
Proof.
  elim: mu => [//=|[q a] mu IH] //=.
  by rewrite IH scale_app !scale_scale.
Qed.

Lemma bind_Enum_assoc {A B C}
    (mu : Enum A) (k : A -> Enum B) (h : B -> Enum C) :
  bind_Enum (bind_Enum mu k) h =
  bind_Enum mu (fun x => bind_Enum (k x) h).
Proof.
  elim: mu => [//=|[p a] mu IH] //=.
  by rewrite bind_Enum_app bind_Enum_scale IH.
Qed.

Lemma bind_Enum_ext {A B}
    (mu : Enum A) (k1 k2 : A -> Enum B) :
  (forall x, k1 x = k2 x) ->
  bind_Enum mu k1 = bind_Enum mu k2.
Proof.
  move=> Hk.
  elim: mu => [//=|[p a] mu IH] //=.
  by rewrite Hk IH.
Qed.
