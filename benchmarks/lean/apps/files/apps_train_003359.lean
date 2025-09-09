-- <vc-helpers>
-- </vc-helpers>

def owned_cat_and_dog (cat_years : Nat) (dog_years : Nat) : List Nat
:= sorry

theorem owned_cat_and_dog_output_types (cat_years dog_years : Nat) :
  let result := owned_cat_and_dog cat_years dog_years
  result.length = 2 ∧ ∀ x ∈ result, x ≥ 0
:= sorry

theorem owned_cat_and_dog_monotonic (cat_years dog_years : Nat) :
  let result1 := owned_cat_and_dog cat_years dog_years
  let result2 := owned_cat_and_dog (cat_years + 4) (dog_years + 5)
  result2[0]! ≥ result1[0]! ∧ result2[1]! ≥ result1[1]!
:= sorry

theorem owned_cat_and_dog_zero_years (cat_years dog_years : Nat) :
  cat_years ≤ 14 → dog_years ≤ 14 → owned_cat_and_dog cat_years dog_years = [0, 0]
:= sorry

theorem owned_cat_and_dog_formula (cat_years dog_years : Nat) :
  cat_years ≥ 24 → dog_years ≥ 24 →
  let result := owned_cat_and_dog cat_years dog_years
  result[0]! = 2 + (cat_years - 24) / 4 ∧ result[1]! = 2 + (dog_years - 24) / 5
:= sorry

/-
info: [0, 0]
-/
-- #guard_msgs in
-- #eval owned_cat_and_dog 9 7

/-
info: [2, 2]
-/
-- #guard_msgs in
-- #eval owned_cat_and_dog 24 24

/-
info: [10, 10]
-/
-- #guard_msgs in
-- #eval owned_cat_and_dog 56 64

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible