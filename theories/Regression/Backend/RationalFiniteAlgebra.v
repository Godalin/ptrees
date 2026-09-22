(** Completion work: common scaling/bind, atoms and scalar transport.
    Historical recursions check exact native data, not only observations. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq fintype bigop ssralg ssrnum order rat reals.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist FiniteListAlgebra FiniteAtoms FiniteScalarMap.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Prob.Legacy.RatSubTypes.nnQ.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
From PTree.Prob.Legacy Require Import RatSubTypes.
From PTree.Prob.Backend.EnumQ Require Import Representation Bind Iteration FinitePresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Fixpoint reference_scale {W A} (mul : W -> W -> W) (r : W) (mu : list (W*A)) : list (W*A) :=
  match mu with [::] => [::] | (s,x)::tl => (mul r s,x)::reference_scale mul r tl end.
Definition reference_bind {W A B} (mul : W -> W -> W) (mu : list(W*A)) (k : A -> list(W*B)) :=
  foldr (fun '(p,x) tl => reference_scale mul p (k x) ++ tl) [::] mu.
Lemma reference_scale_shared {W A} mul p (mu : list(W*A)) :
  reference_scale mul p mu = finite_scale_with mul p mu.
Proof. by elim: mu=> [|[q x] tl IH] //=; rewrite IH. Qed.
Lemma reference_bind_shared {W A B} mul (mu : list(W*A)) (k : A -> list(W*B)) :
  reference_bind mul mu k = finite_bind_with mul mu k.
Proof. by elim: mu=> [|[p x] tl IH] //=; rewrite reference_scale_shared IH. Qed.
Example native_scale_exact {A} p (Hp : 0 <= p) (mu : EnumQ A) :
  enumQ_raw (scale_EnumQ Hp mu) = reference_scale (fun p q : rat => p*q) p (enumQ_raw mu).
Proof.
  change (finite_weight_map p (enumQ_raw mu) = reference_scale (fun p q : rat => p*q) p (enumQ_raw mu)).
  by elim: (enumQ_raw mu)=> [|[q x] tl IH] //=; rewrite IH.
Qed.
Example native_bind_exact {A B} (mu : EnumQ A) (k : A -> EnumQ B) :
  enumQ_raw (bind_EnumQ mu k) = reference_bind (fun p q : rat => p*q) (enumQ_raw mu) (fun x => enumQ_raw (k x)).
Proof.
  change (finite_bind (enumQ_raw mu) (fun x => enumQ_raw(k x)) =
    reference_bind (fun p q : rat => p*q) (enumQ_raw mu) (fun x => enumQ_raw(k x))).
  by rewrite -finite_bind_with_numeric reference_bind_shared.
Qed.
Example ordinary_scalar_scale {A} (p : nnQ) (mu : list(nnQ*A)) :
  List.map (fun px => (Qval px.1, px.2)) (reference_scale (fun p q : nnQ => p*q) p mu) =
  finite_weight_map (Qval p) (List.map (fun px => (Qval px.1, px.2)) mu).
Proof.
  rewrite reference_scale_shared -finite_scale_with_weight_map; apply finite_scale_with_scalar_map=> a b; reflexivity.
Qed.
Example ordinary_scalar_bind {A B} (mu : list(nnQ*A)) (k : A -> list(nnQ*B)) :
  List.map (fun px => (Qval px.1, px.2)) (reference_bind (fun p q : nnQ => p*q) mu k) =
  finite_bind (List.map (fun px => (Qval px.1, px.2)) mu)
    (fun x => List.map (fun px => (Qval px.1, px.2)) (k x)).
Proof.
  rewrite reference_bind_shared -finite_bind_with_numeric; apply finite_bind_with_scalar_map=> a b; reflexivity.
Qed.
Example bind_keeps_zero_blocks_and_duplicates :
  finite_bind_with (fun p q : rat => p*q) [:: (0,false); (1,true); (1,true)]
    (fun b => [:: (2,b); (0,b)]) =
  [:: (0,false); (0,false); (2,true); (0,true); (2,true); (0,true)].
Proof. reflexivity. Qed.
Example duplicate_atom_mass :
  finite_atom true [:: ((1:rat),true); (0,true); (2,false); (3,true)] = 4.
Proof. by vm_compute. Qed.
Example atom_observations_agree {A : finType} (mu : EnumQ A) f :
  enumQ_expect f mu = \sum_x finite_atom x (enumQ_raw mu) * f x.
Proof. by rewrite enumQ_expect_finite finite_expect_by_atoms. Qed.

Section ScalarTransport.
Variable R : realType.
Local Definition rat_to_real : {rmorphism rat -> R} := [the {rmorphism rat -> R} of ratr].
Local Lemma rat_to_real_mono : forall x y, x <= y -> rat_to_real x <= rat_to_real y.
Proof. move=> x y H; by rewrite /rat_to_real /= ler_rat. Qed.

Example ordinary_q_to_r_mass {A} (mu : FiniteSubdist rat_rat__canonical__Num_NumDomain A) :
  finite_subdist_expect (finite_subdist_map_weights rat_to_real_mono mu) (fun _ => 1) =
  ratr (finite_subdist_expect mu (fun _ => 1)).
Proof. exact: finite_map_weights_mass. Qed.
Example ordinary_q_to_r_bind {A B} (mu : FiniteSubdist rat_rat__canonical__Num_NumDomain A)
    (k : A -> FiniteSubdist rat_rat__canonical__Num_NumDomain B) :
  finite_enum_raw (finite_subdist_enum (finite_subdist_map_weights rat_to_real_mono (finite_subdist_bind mu k))) =
  finite_enum_raw (finite_subdist_enum (finite_subdist_bind
    (finite_subdist_map_weights rat_to_real_mono mu) (fun x => finite_subdist_map_weights rat_to_real_mono (k x)))).
Proof. exact: finite_subdist_map_weights_bind. Qed.
End ScalarTransport.
