-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def RotateRight (l : Array Int) (n : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem RotateRight_spec (l : Array Int) (n : Int) :
n ≥ 0 →
let r := RotateRight l n
(r.size = l.size) ∧
(∀ i, 0 ≤ i ∧ i < l.size →
r[i]! = l[((i - n + l.size) % l.size).toNat]!) :=
sorry
-- </vc-theorems>