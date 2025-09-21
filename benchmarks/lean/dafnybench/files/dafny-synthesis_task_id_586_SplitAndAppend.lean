-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SplitAndAppend (l : Array Int) (n : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SplitAndAppend_spec (l : Array Int) (n : Int) :
n ≥ 0 ∧ n < l.size →
let r := SplitAndAppend l n
r.size = l.size ∧
∀ i, 0 ≤ i ∧ i < l.size → r[i]! = l[(((i + n) % l.size).toNat)]! :=
sorry
-- </vc-theorems>