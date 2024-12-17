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

Declare Scope pGCL_scope.

Inductive expr :=
| lit (n : nat).

Inductive stmt :=
| skip
| diverge
| assign (n : nat) (e : expr).