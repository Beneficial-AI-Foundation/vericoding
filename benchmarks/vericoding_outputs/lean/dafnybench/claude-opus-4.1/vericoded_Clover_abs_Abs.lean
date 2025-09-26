import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No helpers needed for this simple case
-- </vc-helpers>

-- <vc-definitions>
def Abs (x : Int) : Int :=
if x ≥ 0 then x else -x
-- </vc-definitions>

-- <vc-theorems>
theorem Abs_spec (x : Int) :
(x ≥ 0 → Abs x = x) ∧
(x < 0 → x + Abs x = 0) :=
by
  constructor
  · intro h
    simp [Abs, h]
  · intro h
    simp [Abs]
    split_ifs with h'
    · omega
    · ring
-- </vc-theorems>
