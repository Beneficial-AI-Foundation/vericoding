def valid_mersenne (n : Int) : Bool := sorry

theorem valid_mersenne_returns_bool (n : Int) :
  valid_mersenne n = true ∨ valid_mersenne n = false := sorry

-- <vc-helpers>
-- </vc-helpers>

def valid_mersenne_numbers : List Int :=
  [2,3,5,7,13,17,19,31,61,89,107,127,521,607,1279]

theorem valid_mersenne_outside_range {n : Int} :
  (n < 1 ∨ n > 1279) → valid_mersenne n = false := sorry

theorem valid_mersenne_deterministic (n : Int) :
  valid_mersenne n = valid_mersenne n := sorry

theorem valid_mersenne_in_set {n : Int} :
  1 ≤ n ∧ n ≤ 1279 →
  valid_mersenne n = true ↔ n ∈ valid_mersenne_numbers := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval valid_mersenne 3

/-
info: False
-/
-- #guard_msgs in
-- #eval valid_mersenne 11

/-
info: True
-/
-- #guard_msgs in
-- #eval valid_mersenne 127

-- Apps difficulty: introductory
-- Assurance level: unguarded