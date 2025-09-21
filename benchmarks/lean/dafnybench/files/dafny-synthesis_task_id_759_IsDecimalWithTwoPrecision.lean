-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsDecimalWithTwoPrecision (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsDecimalWithTwoPrecision_spec (s : String) :
let result := IsDecimalWithTwoPrecision s
(result → ∃ i, 0 ≤ i ∧ i < s.length ∧ s.get ⟨i⟩ = '.' ∧ s.length - i - 1 = 2) ∧
(!result → ¬(∃ i, 0 ≤ i ∧ i < s.length ∧ s.get ⟨i⟩ = '.' ∧ s.length - i - 1 = 2)) :=
sorry
-- </vc-theorems>