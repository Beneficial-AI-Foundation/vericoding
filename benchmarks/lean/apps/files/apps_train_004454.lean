-- <vc-helpers>
-- </vc-helpers>

def human_years_cat_years_dog_years (human_years : Int) : List Int := sorry

theorem conversion_properties (human_years : Int) (h : human_years ≥ 1) :
  let result := human_years_cat_years_dog_years human_years
  -- Result is a list of length 3 with integer elements
  result.length = 3 ∧
  -- First element matches input
  result[0]! = human_years ∧
  -- Cat and dog years are non-negative
  result[1]! ≥ 0 ∧ 
  result[2]! ≥ 0 ∧
  -- Dog years relation to cat years
  (human_years > 2 → result[2]! ≥ result[1]!) ∧
  (human_years ≤ 2 → result[2]! = result[1]!) ∧
  -- Growth rates after year 2
  (human_years > 2 → 
    result[1]! - 24 = (human_years - 2) * 4 ∧
    result[2]! - 24 = (human_years - 2) * 5) :=
sorry

/-
info: [1, 15, 15]
-/
-- #guard_msgs in
-- #eval human_years_cat_years_dog_years 1

/-
info: [2, 24, 24]
-/
-- #guard_msgs in
-- #eval human_years_cat_years_dog_years 2

/-
info: [10, 56, 64]
-/
-- #guard_msgs in
-- #eval human_years_cat_years_dog_years 10

-- Apps difficulty: introductory
-- Assurance level: guarded