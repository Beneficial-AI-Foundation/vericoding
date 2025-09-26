-- <vc-preamble>
def List.sum (xs : List Int) : Int := 
  xs.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def learn_charitable_game (arr : List Int) : Bool := sorry

theorem single_element_validity {n : Int} :
  learn_charitable_game [n] = (n > 0) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_positive_sum_invalid {arr : List Int} (h : arr.sum ≤ 0) :
  learn_charitable_game arr = false := sorry

theorem divisible_sum_valid {arr : List Int} (h₁ : arr.sum > 0) :
  learn_charitable_game arr = (arr.sum % arr.length == 0) := sorry

theorem all_zeros_invalid {arr : List Int} 
  (h₁ : arr.length ≥ 2)
  (h₂ : ∀ x ∈ arr, x = 0) :
  learn_charitable_game arr = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval learn_charitable_game [0, 56, 100]

/-
info: False
-/
-- #guard_msgs in
-- #eval learn_charitable_game [0, 0, 0]

/-
info: True
-/
-- #guard_msgs in
-- #eval learn_charitable_game [11]
-- </vc-theorems>