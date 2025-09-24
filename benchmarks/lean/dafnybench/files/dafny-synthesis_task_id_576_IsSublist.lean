-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsSublist (sub : Array Int) (main : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsSublist_spec (sub main : Array Int) :
∃ i, 0 ≤ i ∧ i ≤ main.size - sub.size ∧
(∀ j, 0 ≤ j ∧ j < sub.size → sub[j]! = main[i + j]!) →
IsSublist sub main = true :=
sorry
-- </vc-theorems>