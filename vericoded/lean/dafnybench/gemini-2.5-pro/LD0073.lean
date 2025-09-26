import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No helpers are needed for this file.
-- </vc-helpers>

-- <vc-definitions>
def Min_ (x y : Int) : Int :=
if x ≤ y then x else y
-- </vc-definitions>

-- <vc-theorems>
theorem Min_spec (x y z : Int) :
z = Min_ x y →
((x ≤ y → z = x) ∧
(x > y → z = y)) :=
by
  -- Given `z = Min_ x y`, we can substitute `z`.
  rintro rfl
  -- Unfold the definition of `Min_` to see the `if-then-else` expression.
  unfold Min_
  -- Split the proof into two cases based on the condition `x ≤ y`.
  split_ifs
  -- In each case, `simp_all` can automatically prove the goal
  -- using the available hypothesis (`x ≤ y` or `¬(x ≤ y)`).
  · simp_all
  · simp_all
-- </vc-theorems>
