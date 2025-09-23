-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def AppendArrayToSeq (s : Array Int) (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem AppendArrayToSeq_spec (s : Array Int) (a : Array Int) :
let r := AppendArrayToSeq s a
r.size = s.size + a.size ∧
(∀ i, 0 ≤ i ∧ i < s.size → r[i]! = s[i]!) ∧
(∀ i, 0 ≤ i ∧ i < a.size → r[s.size + i]! = a[i]!) :=
sorry
-- </vc-theorems>