-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Mid (p q : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Mid_spec (p q : Int) :
p ≤ q →
let m := Mid p q
(p ≤ m ∧ m ≤ q) ∧
(m - p ≤ q - m) ∧
(0 ≤ (q - m) - (m - p) ∧ (q - m) - (m - p) ≤ 1) :=
sorry
-- </vc-theorems>