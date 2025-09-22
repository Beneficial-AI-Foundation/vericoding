-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MaxLengthList (lists : Array (Array Int)) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem MaxLengthList_spec (lists : Array (Array Int)) (maxList : Array Int) :
lists.size > 0 →
(∀ l, l ∈ lists → l.size ≤ maxList.size) ∧
maxList ∈ lists :=
sorry
-- </vc-theorems>