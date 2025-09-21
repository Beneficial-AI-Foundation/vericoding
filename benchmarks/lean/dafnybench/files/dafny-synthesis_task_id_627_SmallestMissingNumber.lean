-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SmallestMissingNumber (s : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SmallestMissingNumber_spec (s : Array Int) :
(∀ i j, 0 ≤ i → i < j → j < s.size → s[i]! ≤ s[j]!) →
(∀ i, 0 ≤ i → i < s.size → s[i]! ≥ 0) →
let v := SmallestMissingNumber s
0 ≤ v ∧
(∀ i, 0 ≤ i → i < s.size → s[i]! ≠ v) ∧
(∀ k, 0 ≤ k → k < v → ∃ i, 0 ≤ i ∧ i < s.size ∧ s[i]! = k) :=
sorry
-- </vc-theorems>