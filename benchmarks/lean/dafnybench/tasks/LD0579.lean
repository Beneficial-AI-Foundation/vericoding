-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def AbsIt (s : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem AbsIt_spec (s : Array Int) :
let s' := AbsIt s
(∀ i, 0 ≤ i ∧ i < s.size →
(if s[i]! < 0 then s'[i]! = -(s[i]!) else s'[i]! = s[i]!)) ∧
s'.size = s.size :=
sorry
-- </vc-theorems>