import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Helper lemmas for Int multiplication
theorem helper_mul_zero (x : Int) : x * 0 = 0 := by simp

theorem helper_mul_one (x : Int) : x * 1 = x := by simp

-- </vc-helpers>

-- <vc-definitions>
def Multiply (a b : Int) : Int :=
a * b
-- </vc-definitions>

-- <vc-theorems>
theorem Multiply_spec (a b : Int) :
Multiply a b = a * b :=
by rfl
-- </vc-theorems>
