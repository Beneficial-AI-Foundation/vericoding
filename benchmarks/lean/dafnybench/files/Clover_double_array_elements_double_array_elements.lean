-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def double_array_elements (s : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem double_array_elements_spec (s : Array Int) :
∀ i, 0 ≤ i ∧ i < s.size →
(double_array_elements s)[i]! = 2 * s[i]! :=
sorry
-- </vc-theorems>