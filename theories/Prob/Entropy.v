Require Import Reals.

Local Open Scope R.

Definition Entropy := nat -> { r : R | 0 <= r <= 1 }.
Print Entropy.