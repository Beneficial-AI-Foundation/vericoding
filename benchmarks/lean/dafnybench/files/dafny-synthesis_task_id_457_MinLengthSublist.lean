-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MinLengthSublist (s : Array (Array Int)) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem MinLengthSublist_spec (s : Array (Array Int)) :
s.size > 0 →
(∃ i, i < s.size ∧ MinLengthSublist s = s[i]!) ∧
(∀ sublist, (∃ i, i < s.size ∧ sublist = s[i]!) →
(MinLengthSublist s).size ≤ sublist.size) :=
sorry
-- </vc-theorems>