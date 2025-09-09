-- <vc-helpers>
-- </vc-helpers>

def is_rainbow_array (arr : List Int) : String := sorry

def is_palindrome (arr : List α) : Bool := sorry

theorem rainbow_array_palindrome_property (arr : List Int) :
  is_rainbow_array arr = "yes" →
  is_palindrome arr = true ∧ 
  (∀ x ∈ arr, 1 ≤ x ∧ x ≤ 7) ∧
  (∀ n, 1 ≤ n ∧ n ≤ 7 → n ∈ arr) := sorry

theorem rainbow_array_invalid_inputs (arr : List Int) : 
  is_rainbow_array arr = "yes" →
  (∀ x ∈ arr, 1 ≤ x ∧ x ≤ 7) ∧
  is_palindrome arr = true ∧
  (∀ n, 1 ≤ n ∧ n ≤ 7 → n ∈ arr) := sorry

theorem incomplete_numbers (arr : List Int)
  (h : ∃ n, 1 ≤ n ∧ n ≤ 7 ∧ n ∉ arr) :
  is_rainbow_array arr = "no" := sorry

theorem non_palindrome (arr : List Int) (h : arr ≠ []) :
  let first := arr.head!
  let new_val := if first < 7 then first + 1 else first - 1
  is_rainbow_array (arr ++ [new_val]) = "no" := sorry

/-
info: 'yes'
-/
-- #guard_msgs in
-- #eval is_rainbow_array [1, 2, 3, 4, 4, 5, 6, 6, 6, 7, 6, 6, 6, 5, 4, 4, 3, 2, 1]

/-
info: 'no'
-/
-- #guard_msgs in
-- #eval is_rainbow_array [1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 1]

/-
info: 'no'
-/
-- #guard_msgs in
-- #eval is_rainbow_array [1, 2, 3, 4, 5, 6, 8, 6, 5, 4, 3, 2, 1]

-- Apps difficulty: interview
-- Assurance level: unguarded