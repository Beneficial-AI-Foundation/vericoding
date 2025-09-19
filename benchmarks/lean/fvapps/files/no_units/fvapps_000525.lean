-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_moves_to_exit (n: Nat) : Nat := sorry

theorem min_moves_always_positive (n: Nat) (h: n > 0): 
  min_moves_to_exit n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_moves_even_case (n: Nat) (h1: n > 0) (h2: n % 2 = 0):
  min_moves_to_exit n = n * 4 := sorry

theorem min_moves_mod4_three_case (n: Nat) (h1: n > 0) (h2: n % 4 = 3):
  min_moves_to_exit n = n := sorry

theorem min_moves_other_case (n: Nat) (h1: n > 0) (h2: n % 2 ≠ 0) (h3: n % 4 ≠ 3):
  min_moves_to_exit n = n * 2 := sorry

theorem min_moves_bounded_by_perimeter (n: Nat) (h: n > 0):
  min_moves_to_exit n ≤ 4 * n := sorry

theorem min_moves_specific_cases :
  min_moves_to_exit 1 = 2 ∧
  min_moves_to_exit 2 = 8 ∧
  min_moves_to_exit 3 = 3 ∧
  min_moves_to_exit 4 = 16 ∧
  min_moves_to_exit 7 = 7 := sorry
-- </vc-theorems>