import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def SquareRoot (N : Nat) : Nat :=
Nat.sqrt N
-- </vc-definitions>

-- <vc-theorems>
theorem SquareRoot_spec (N : Nat) :
let r := SquareRoot N
r * r ≤ N ∧ N < (r + 1) * (r + 1) :=
by exact And.intro (Nat.sqrt_le N) (Nat.lt_succ_sqrt N)
-- </vc-theorems>
