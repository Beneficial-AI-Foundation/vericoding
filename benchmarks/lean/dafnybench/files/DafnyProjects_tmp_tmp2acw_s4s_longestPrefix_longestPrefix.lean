-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestPrefix (a b : Array Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem longestPrefix_spec (a b : Array Int) (i : Nat) :
let i := longestPrefix a b
i ≤ a.size ∧ i ≤ b.size ∧
(i < a.size ∧ i < b.size → a[i]! ≠ b[i]!) :=
sorry
-- </vc-theorems>