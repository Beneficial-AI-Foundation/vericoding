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
-- </vc-theorems>