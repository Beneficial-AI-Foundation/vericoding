import Mathlib
-- <vc-preamble>
partial def power (a : Int) (n : Int) : Int :=
if n == 0 then 1 else a * power a (n - 1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helpers needed for this file.
-- </vc-helpers>

-- <vc-definitions>
def A8Q1 (y0 : Int) (x : Int) : Int :=
power x y0
-- </vc-definitions>

-- <vc-theorems>
theorem A8Q1_spec (y0 : Int) (x : Int) :
y0 ≥ 0 → A8Q1 y0 x = power x y0 :=
by intro _; rfl
-- </vc-theorems>
