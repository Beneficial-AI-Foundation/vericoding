import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No helper definitions needed for this simple Min function
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
  intro h
  constructor
  · intro hle
    rw [h, Min_]
    simp [if_pos hle]
  · intro hgt
    rw [h, Min_]
    simp [if_neg (not_le_of_gt hgt)]
-- </vc-theorems>
