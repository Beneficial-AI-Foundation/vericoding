-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MinSecondValueFirst (s : Array (Array Int)) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem MinSecondValueFirst_spec (s : Array (Array Int)) :
s.size > 0 ∧
(∀ i, 0 ≤ i ∧ i < s.size → s[i]!.size ≥ 2) →
∃ i, 0 ≤ i ∧ i < s.size ∧
MinSecondValueFirst s = (s[i]!)[0]! ∧
(∀ j, 0 ≤ j ∧ j < s.size → (s[i]!)[1]! ≤ (s[j]!)[1]!) :=
sorry
-- </vc-theorems>