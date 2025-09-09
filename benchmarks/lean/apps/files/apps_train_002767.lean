-- <vc-helpers>
-- </vc-helpers>

def combs_non_empty_boxesII (n : Nat) : List Nat := sorry

-- Output has length 3 and contains only natural numbers

theorem output_structure (n : Nat) (h : n > 0) (h2 : n ≤ 20) : 
  let result := combs_non_empty_boxesII n
  result.length = 3 ∧ (∀ x ∈ result, x ≥ 0) := sorry

-- First element is positive

theorem first_value_positive (n : Nat) (h : n > 0) (h2 : n ≤ 20) :
  (combs_non_empty_boxesII n).get! 0 > 0 := sorry

-- Second element is less than or equal to first element

theorem second_value_less_than_first (n : Nat) (h : n > 0) (h2 : n ≤ 20) :
  (combs_non_empty_boxesII n).get! 1 ≤ (combs_non_empty_boxesII n).get! 0 := sorry

-- Third element is in valid range

theorem index_in_valid_range (n : Nat) (h : n > 0) (h2 : n ≤ 20) :
  let result := (combs_non_empty_boxesII n).get! 2
  1 ≤ result ∧ result ≤ n := sorry

-- Minimal case when n = 1

theorem minimal_case :
  combs_non_empty_boxesII 1 = [1, 1, 1] := sorry

-- Monotonic first value

theorem monotonic_first_value (n : Nat) (h : n > 1) (h2 : n ≤ 20) :
  (combs_non_empty_boxesII (n-1)).get! 0 < (combs_non_empty_boxesII n).get! 0 := sorry

/-
info: [15, 7, 2]
-/
-- #guard_msgs in
-- #eval combs_non_empty_boxesII 4

/-
info: [5, 3, 2]
-/
-- #guard_msgs in
-- #eval combs_non_empty_boxesII 3

/-
info: [2, 1, 2]
-/
-- #guard_msgs in
-- #eval combs_non_empty_boxesII 2

-- Apps difficulty: introductory
-- Assurance level: unguarded