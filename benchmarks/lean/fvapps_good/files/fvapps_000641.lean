-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_special_factorial_number (n : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem special_factorial_returns_binary (n : Int) :
  let result := is_special_factorial_number n
  result = 0 ∨ result = 1 := by
  sorry

theorem special_factorial_consistency (n : Int) :
  is_special_factorial_number n = is_special_factorial_number n := by
  sorry

theorem known_special_factorials :
  is_special_factorial_number 1 = 1 ∧
  is_special_factorial_number 2 = 1 ∧ 
  is_special_factorial_number 145 = 1 ∧
  is_special_factorial_number 40585 = 1 := by
  sorry

theorem non_special_factorials (n : Int) :
  n ≠ 1 →
  n ≠ 2 →
  n ≠ 145 →
  n ≠ 40585 →
  is_special_factorial_number n = 0 := by
  sorry
-- </vc-theorems>