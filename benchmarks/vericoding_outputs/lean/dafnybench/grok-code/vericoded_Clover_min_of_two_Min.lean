import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

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
  intro h_eq
  constructor
  · intro h
    rw [Min_] at h_eq
    rw [if_pos h] at h_eq
    exact h_eq
  · intro h
    rw [Min_] at h_eq
    rw [if_neg (not_le_of_gt h)] at h_eq
    exact h_eq
-- </vc-theorems>
