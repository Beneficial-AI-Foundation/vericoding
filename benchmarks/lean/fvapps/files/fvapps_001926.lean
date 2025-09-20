-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digitSum (n : Int) : Int := sorry
def find_numbers (n : Int) : List Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_numbers_valid_values {n : Int} (h : 0 ≤ n ∧ n ≤ 10000) :
  let result := find_numbers n
  ∀ x ∈ result,
    (0 ≤ x ∧ x ≤ n) ∧ 
    (x + digitSum x = n) := sorry

theorem find_numbers_negative_input {n : Int} (h : n < 0) :
  find_numbers n = [] := sorry

theorem find_numbers_window_size {n : Int} (h : 0 ≤ n ∧ n ≤ 10000) :
  let result := find_numbers n
  ∀ x ∈ result,
    x ≥ max 0 (n - 100) ∧ x ≤ n := sorry

theorem find_numbers_known_cases :
  find_numbers 21 = [15] ∧
  find_numbers 20 = [] ∧
  find_numbers 39 = [33] := sorry
-- </vc-theorems>