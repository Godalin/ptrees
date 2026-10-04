(** Serializable input for the existing shallow pGCL language. This is an
    input elaborator, not a second operational or distribution semantics.
    The simulator fixes integer stores and rational probability parameters;
    [command S P] and all generic theorems remain unchanged. *)
From Coq Require Import Utf8 ZArith List Bool.
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssralg ssrnum rat.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.FreeOmega Require Import Measure.
From PTree.Eq Require Import PTreeKernel.
From PTree.Interp Require Import ReturnIteration.
From PTree.Examples.PGCL Require Import Syntax Finite Interpretation Forward.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition pgcl := command store rational_probability.

Inductive arithmetic :=
| Number (z : Z)
| Read (x : nat)
| Plus (a b : arithmetic)
| Minus (a b : arithmetic)
| Times (a b : arithmetic).

Inductive condition :=
| Boolean (b : bool)
| Equal (a b : arithmetic)
| Less (a b : arithmetic)
| LessEqual (a b : arithmetic)
| Not (b : condition)
| And (a b : condition)
| Or (a b : condition).

Fixpoint eval_arithmetic (e : arithmetic) (s : store) : Z :=
  match e with
  | Number z => z | Read x => s x
  | Plus a b => Z.add (eval_arithmetic a s) (eval_arithmetic b s)
  | Minus a b => Z.sub (eval_arithmetic a s) (eval_arithmetic b s)
  | Times a b => Z.mul (eval_arithmetic a s) (eval_arithmetic b s)
  end.

Fixpoint eval_condition (b : condition) (s : store) : bool :=
  match b with
  | Boolean v => v
  | Equal a b => Z.eqb (eval_arithmetic a s) (eval_arithmetic b s)
  | Less a b => Z.ltb (eval_arithmetic a s) (eval_arithmetic b s)
  | LessEqual a b => Z.leb (eval_arithmetic a s) (eval_arithmetic b s)
  | Not b => negb (eval_condition b s)
  | And a b => andb (eval_condition a s) (eval_condition b s)
  | Or a b => orb (eval_condition a s) (eval_condition b s)
  end.

Inductive source :=
| Skip | Diverge
| Assign (x : nat) (e : arithmetic)
| Sequence (a b : source)
| If (b : condition) (yes no : source)
| Choice (numerator denominator : nat) (left right : source)
| While (b : condition) (body : source).

(** Reject zero denominators and out-of-range probabilities BEFORE execution,
    even in unreachable branches. No floating point or normalization. *)
Definition check_probability (n d : nat) : option rational_probability.
Proof.
  destruct (Nat.eqb d 0) eqn:Hd; [exact None|].
  destruct (Nat.leb n d) eqn:Hnd; [|exact None].
  set (q := (n%:R / d%:R : rat)).
  destruct (Bool.bool_dec (0 <= q) true) as [Hn|Hn]; [|exact None].
  destruct (Bool.bool_dec (q <= 1) true) as [Hb|Hb]; [|exact None].
  exact (Some (@Probability _ q Hn Hb)).
Defined.

Fixpoint compile (c : source) : option pgcl :=
  match c with
  | Skip => Some CSkip | Diverge => Some CDiverge
  | Assign x e => Some (assign x (eval_arithmetic e))
  | Sequence a b =>
      match compile a, compile b with
      | Some a, Some b => Some (CSeq a b) | _, _ => None end
  | If b yes no =>
      match compile yes, compile no with
      | Some yes, Some no => Some (CIf (eval_condition b) yes no)
      | _, _ => None end
  | Choice n d l r =>
      match check_probability n d, compile l, compile r with
      | Some p, Some l, Some r => Some (CChoice p l r)
      | _, _, _ => None end
  | While b body =>
      match compile body with
      | Some body => Some (CWhile (eval_condition b) body) | None => None end
  end.

(** Zero-initialized store, with later entries overriding earlier ones. *)
Definition initial_store (entries : list (nat * Z)) : store :=
  List.fold_left (λ s entry, update s (fst entry) (snd entry)) entries (λ _, 0%Z).

Example reject_zero_denominator : check_probability 1 0 = None.
Proof. reflexivity. Qed.
Example reject_overweight : check_probability 3 2 = None.
Proof. reflexivity. Qed.
Example reject_unreachable_bad_choice :
  compile (If (Boolean true) Skip (Choice 1 0 Skip Skip)) = None.
Proof. reflexivity. Qed.
Example store_last_write : initial_store ((0, 2%Z) :: (0, 3%Z) :: nil) 0 = 3%Z.
Proof. reflexivity. Qed.

(** A successful checked input uses the existing forward semantics. The
    compile premise is the frontend entry condition; the semantic result
    already holds for every well-typed [pgcl] command. This wrapper neither
    specifies the textual parser nor proves preservation of an independent
    source semantics. Execution still follows [run], including State interp. *)
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).

Theorem compile_hitting (src : source) (c : pgcl) (s : store) :
  compile src = Some c →
  ptree_stable_hitting (FI := FI) (FO := FO)
    (observe (run (E := void1) rational_coin c s))
    (iteration_return_map (E := void1) (MN := SubEnumQ)
      (denote (FI := FI) (FO := FO) rational_coin c s)).
Proof. intros _. apply rational_pgcl_hitting. Qed.
