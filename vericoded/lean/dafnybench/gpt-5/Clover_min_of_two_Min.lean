import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem gt_implies_not_le {a b : Int} (h : a > b) : ¬ a ≤ b :=
  not_le_of_gt h

-- LLM HELPER
theorem if_min_eq_left_of_le {a b : Int} (h : a ≤ b) :
    (if a ≤ b then a else b) = a := by simp [h]

-- LLM HELPER
theorem if_min_eq_right_of_gt {a b : Int} (h : a > b) :
    (if a ≤ b then a else b) = b := by
  have : ¬ a ≤ b := not_le_of_gt h
  simp [this]

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
  intro hz
  subst hz
  constructor
  · intro hxy
    simp [Min_, hxy]
  · intro hxgt
    have hxnot : ¬ x ≤ y := not_le_of_gt hxgt
    simp [Min_, hxnot]

-- </vc-theorems>
