-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_classroom_shuffle (n m : Nat) : String := sorry

theorem solve_classroom_shuffle_is_valid (n m : Nat) 
  (h1 : n ≥ 1) (h2 : m ≥ 1) : 
  solve_classroom_shuffle n m = "YES" ∨ solve_classroom_shuffle n m = "NO" :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_classroom_shuffle_even_dimension 
  (n : Nat) (h : n ≥ 1) :
  solve_classroom_shuffle n 2 = "YES" ∧ solve_classroom_shuffle 2 n = "YES" := 
sorry

theorem solve_classroom_shuffle_odd_dimensions 
  (n m : Nat) (h1 : n ≥ 1) (h2 : m ≥ 1) :
  (n % 2 = 1 ∧ m % 2 = 1 → solve_classroom_shuffle n m = "NO") ∧
  (n % 2 = 0 ∨ m % 2 = 0 → solve_classroom_shuffle n m = "YES") :=
sorry

theorem solve_classroom_shuffle_small_grids :
  solve_classroom_shuffle 1 1 = "NO" ∧ 
  solve_classroom_shuffle 1 2 = "YES" ∧
  solve_classroom_shuffle 2 1 = "YES" :=
sorry
-- </vc-theorems>