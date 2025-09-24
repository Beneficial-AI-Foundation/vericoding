-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def below_zero (operations : Array Int) : Array Int × Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem below_zero_spec (operations : Array Int) :
let (s, result) := below_zero operations
s.size = operations.size + 1 ∧
s[0]! = 0 ∧
(∀ i, 0 ≤ i ∧ i < s.size - 1 → s[i+1]! = s[i]! + operations[i]!) ∧
(result = true → ∃ i, 1 ≤ i ∧ i ≤ operations.size ∧ s[i]! < 0) ∧
(result = false → ∀ i, 0 ≤ i ∧ i < s.size → s[i]! ≥ 0) :=
sorry
-- </vc-theorems>