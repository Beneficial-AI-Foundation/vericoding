-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CountIdenticalPositions (a b c : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem CountIdenticalPositions_spec (a b c : Array Int) :
a.size = b.size ∧ b.size = c.size →
let count := CountIdenticalPositions a b c
count ≥ 0 ∧
∃ positions : List Nat,
(∀ i, i ∈ positions →
0 ≤ i ∧ i < a.size ∧
a[i]! = b[i]! ∧
b[i]! = c[i]!) ∧
count = positions.length :=
sorry
-- </vc-theorems>