-- <vc-preamble>
def allEqual (s : Array Int) : Prop :=
∀ i j, 0 ≤ i ∧ i < s.size ∧ 0 ≤ j ∧ j < s.size → s[i]! = s[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mallEqual1 (v : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mallEqual1_spec (v : Array Int) :
mallEqual1 v = allEqual v :=
sorry
-- </vc-theorems>