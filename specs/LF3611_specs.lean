-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_length_num (digits max_num : Int) : Result := sorry

theorem min_length_num_valid_input (digits max_num : Int)
  (h1 : digits ≥ 1) (h2 : digits ≤ 100)
  (h3 : max_num ≥ 1) (h4 : max_num ≤ 1000) :
  let result := min_length_num digits max_num
  result.success → (
    result.value ≤ max_num ∧
    result.value > 0
  ) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_length_num_invalid_digits (digits max_num : Int)
  (h1 : digits ≤ 0) (h2 : max_num ≥ 1) (h3 : max_num ≤ 1000) :
  min_length_num digits max_num = ⟨false, -1⟩ := sorry

theorem min_length_num_invalid_max_num (digits max_num : Int)
  (h1 : digits ≥ 1) (h2 : digits ≤ 100) (h3 : max_num ≤ 0) :
  min_length_num digits max_num = ⟨false, -1⟩ := sorry

/-
info: [True, 10]
-/
-- #guard_msgs in
-- #eval min_length_num 5 10

/-
info: [False, -1]
-/
-- #guard_msgs in
-- #eval min_length_num 7 11

/-
info: [True, 13]
-/
-- #guard_msgs in
-- #eval min_length_num 7 14
-- </vc-theorems>