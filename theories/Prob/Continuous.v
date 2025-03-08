From PTree.Prob Require Import RealSubTypes.
Open Scope R.

Check 𝕀.

Inductive Sam A :=
| Return (_ : A)
| Sample (_ : 𝕀 -> Sam A).

Arguments Return {_} _.
Arguments Sample {_} _.

Check Return 1.
Check Sample (fun r : 𝕀 => Return 3).

Check Rle.
Check Rle_dec.
Check Sample (fun r => Return (if Rle_dec r (1/2) then 3 else 2)).

