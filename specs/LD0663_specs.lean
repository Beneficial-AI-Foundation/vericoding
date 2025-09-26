-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SmallestListLength (s : Array (Array Int)) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SmallestListLength_spec (s : Array (Array Int)) :
s.size > 0 →
(∀ i, 0 ≤ i ∧ i < s.size → SmallestListLength s ≤ (s[i]!).size) ∧
(∃ i, 0 ≤ i ∧ i < s.size ∧ SmallestListLength s = (s[i]!).size) :=
sorry
-- </vc-theorems>