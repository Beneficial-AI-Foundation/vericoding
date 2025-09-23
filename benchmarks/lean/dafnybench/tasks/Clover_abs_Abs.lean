-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Abs (x : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Abs_spec (x : Int) :
(x ≥ 0 → Abs x = x) ∧
(x < 0 → x + Abs x = 0) :=
sorry
-- </vc-theorems>