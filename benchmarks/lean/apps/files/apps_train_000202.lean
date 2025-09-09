-- <vc-helpers>
-- </vc-helpers>

def predict_the_winner (nums : List Int) : Bool := sorry

theorem empty_or_even_length_wins (nums : List Int) : 
  (nums = []) ∨ (nums.length % 2 = 0) → predict_the_winner nums = true := sorry

theorem equal_elements_wins (nums : List Int) (h1 : nums.length ≥ 2) 
  (h2 : ∀ x ∈ nums, x = nums[0]!) : predict_the_winner nums = true := sorry

theorem reversed_same_result (nums : List Int) (h : nums ≠ []) :
  predict_the_winner nums = predict_the_winner nums.reverse := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval predict_the_winner [1, 5, 2]

/-
info: True
-/
-- #guard_msgs in
-- #eval predict_the_winner [1, 5, 233, 7]

/-
info: True
-/
-- #guard_msgs in
-- #eval predict_the_winner []

-- Apps difficulty: interview
-- Assurance level: unguarded