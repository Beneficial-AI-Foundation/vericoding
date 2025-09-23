-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rotate (a : Array Int) (offset : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rotate_spec (a : Array Int) (offset : Int) :
offset ≥ 0 →
let b := rotate a offset
(b.size = a.size) ∧
(∀ i, 0 ≤ i ∧ i < a.size → b[i]! = a[((i + offset) % a.size).toNat]!) :=
sorry
-- </vc-theorems>