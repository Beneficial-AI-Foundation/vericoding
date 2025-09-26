import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

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
  · -- Case x ≥ 0
    rintro h_ge_zero
    simp [Abs, if_pos h_ge_zero]
  · -- Case x < 0
    rintro h_lt_zero
    have h_not_ge_zero : ¬(x ≥ 0) := by linarith
    simp [Abs, if_neg h_not_ge_zero, Int.add_left_neg]
-- </vc-theorems>
