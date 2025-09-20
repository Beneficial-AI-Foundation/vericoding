-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def owned_cat_and_dog (cat_years : Nat) (dog_years : Nat) : List Nat
:= sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>