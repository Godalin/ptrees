(*|

In this file we formalize the language pGCL:

C → skip                      (effect-less program)
  | diverge                   (freeze)
  | x := E                    (assignment)
  | x :≈ μ                    (random assignment)
  | C # C                     (sequential composition)
  | if ( φ ) { C } else { C } (conditional choice)
  (* | { C } 2 { C }             (nondeterministic choice) *)
  | { C } [p] { C }           (probabilistic choice)
  | while ( φ ) { C }         (while loop)

but without the nondeterministic choice.

|*)

From Coq Require Import ZArith.
From Coq Require Import Reals.
From Coq Require Import List.
Import ListNotations.

From ExtLib Require Import Monad.
Import MonadNotation.

From ITree Require Import ITree.
From ITree Require Import Basics.
From ITree Require Import Events.MapDefault.
From ITree.Core Require Import Subevent.

(* PTree core imports *)
From PTree.Core Require Import PTreeDefinitionFin.
From PTree.Prob Require Import FinSupp.
From PTree.Interp Require Import PState.

(* PTree events imports *)
(* From PTree.Events Require Import Sample. *)



Declare Scope pGCL_scope.

Notation Val := Z.
Notation Var := nat.
Notation Σ := (nat -> Val).

Definition update (σ : Σ) (x : nat) (v : Val) : Σ :=
  fun y => if x =? y then v else σ y.



Section denote_pGCL.
Open Scope Z_scope.

(* language *)

Inductive aexp : Type :=
| var : Var -> aexp
| lit : Val -> aexp
| add : aexp -> aexp -> aexp
| sub : aexp -> aexp -> aexp
| mul : aexp -> aexp -> aexp.

Inductive rexp : Type :=
| ofa : aexp -> rexp
| div : rexp -> rexp -> rexp.

Inductive test : Type :=
| tr : test
| fa : test
| eq : aexp -> aexp -> test
| le : aexp -> aexp -> test
| not : test -> test
| and : test -> test -> test
| or : test -> test -> test.

Inductive stmt : Type :=
| skip : stmt
| diverge : stmt
| assign : Var -> aexp -> stmt
| guard : test -> stmt -> stmt -> stmt
| pchoice : rexp -> stmt -> stmt -> stmt
| seq : stmt -> stmt -> stmt
| loop : test -> stmt -> stmt.



(* Events *)

Variant pstateE : Type -> Type :=
| GetVar (x : nat) : pstateE Val
| SetVar (x : nat) (v : Val) : pstateE unit.

Locate sampleE.

(* denotation of pGCL into itrees *)

Context (eff : Type -> Type).
Context {Has_pstate : pstateE -< eff}.
Context {Has_sample : sampleE -< eff}.



(* denotation of arithmetic expressions *)
Fixpoint denote_aexp (e : aexp) : itree eff Val :=
  match e with
  | var x => trigger (GetVar x)
  | lit i => ret i
  | add e1 e2 =>
    v1 <- denote_aexp e1 ;;
    v2 <- denote_aexp e2 ;;
    ret (v1 + v2)
  | sub e1 e2 =>
    v1 <- denote_aexp e1 ;;
    v2 <- denote_aexp e2 ;;
    ret (v1 - v2)
  | mul e1 e2 => 
    v1 <- denote_aexp e1 ;;
    v2 <- denote_aexp e2 ;;
    ret (v1 * v2)
  end.

Fixpoint denote_rexp (e : rexp) : itree eff R :=
  match e with
  | ofa a => v <- denote_aexp a ;; ret (IZR v)
  | div r1 r2 =>
    v1 <- denote_rexp r1 ;;
    v2 <- denote_rexp r2 ;;
    ret (v1 / v2)%R
  end.



(* denotation of tests *)
Fixpoint denote_test (x : test) : itree eff bool :=
  match x with
  | tr => ret true
  | fa => ret false
  | eq e1 e2 => 
    v1 <- denote_aexp e1 ;;
    v2 <- denote_aexp e2 ;;
    ret (v1 =? v2)
  | le e1 e2 =>
    v1 <- denote_aexp e1 ;;
    v2 <- denote_aexp e2 ;;
    ret (v1 <=? v2)
  | not t => 
    b <- denote_test t ;;
    ret (negb b)
  | and t1 t2 => 
    b1 <- denote_test t1 ;;
    b2 <- denote_test t2 ;;
    ret (andb b1 b2)
  | or t1 t2 =>
    b1 <- denote_test t1 ;;
    b2 <- denote_test t2 ;;
    ret (orb b1 b2)
  end.



(* denotation of statements *)
Fixpoint denote_stmt (s : stmt) : itree eff unit :=
  match s with
  | skip => ret tt
  | diverge => trigger (Sample (mkFinSupp []))
  | assign x e =>
    v <- denote_aexp e ;;
    trigger (SetVar x v)
  | guard t s1 s2 =>
    b <- denote_test t ;;
    match b with 
    | true => denote_stmt s1
    | false => denote_stmt s2
    end
  | pchoice p s1 s2 =>
    pr <- denote_rexp p ;;
    b <- trigger (Sample (pChoice pr true false)) ;;
    match b with
    | true => denote_stmt s1
    | false => denote_stmt s2
    end
  | seq s1 s2 => 
    denote_stmt s1 ;;
    denote_stmt s2
  | loop t s =>
    iter (fun _ => b <- denote_test t ;;
    match b with
    | true => denote_stmt s ;; ret (inl tt)
    | false => ret (inr tt)
    end) tt
  end.

End denote_pGCL.



Module ptree_approach.
Section ptree_approach.
(* denotation of pGCL into ptree *)
Variable eff : Type -> Type.

(* Definition handle_sample : sampleE R ~> ptree eff :=
  fun _ e =>
    match e with
    | Sample μ => meas μ
    end. *)

End ptree_approach.
End ptree_approach.



Definition handle_pstate {E : Type -> Type} `{mapE Var 0%Z -< E}
  : pstateE ~> itree E :=
  fun _ e =>
    match e with
    | GetVar x => lookup_def x
    | SetVar x v => insert x v
    end.

Check handle_sample.

Definition intrep_sample {A : Type} (μ : finSupp A) : pstate Σ A :=
  mkPState (fun σ => (a <- μ ;; ret (a, σ))).
