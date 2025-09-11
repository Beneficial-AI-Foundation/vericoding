-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_numbers_with_even_digits (nums: List Nat) : Nat := sorry

def count_digits (n: Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_numbers_bounds {nums: List Nat} : 
  find_numbers_with_even_digits nums ≤ nums.length := sorry

theorem find_numbers_nonneg {nums: List Nat} :
  find_numbers_with_even_digits nums ≥ 0 := sorry

theorem list_concatenation {nums₁ nums₂: List Nat} :
  find_numbers_with_even_digits (nums₁ ++ nums₂) = 
  find_numbers_with_even_digits nums₁ + find_numbers_with_even_digits nums₂ := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_numbers_with_even_digits [12, 345, 2, 6, 7896]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_numbers_with_even_digits [555, 901, 482, 1771]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_numbers_with_even_digits [1, 22, 333, 4444]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible