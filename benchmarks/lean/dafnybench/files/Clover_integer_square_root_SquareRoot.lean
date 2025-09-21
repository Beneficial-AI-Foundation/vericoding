-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SquareRoot (N : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SquareRoot_spec (N : Nat) :
let r := SquareRoot N
r * r ≤ N ∧ N < (r + 1) * (r + 1) :=
sorry
-- </vc-theorems>