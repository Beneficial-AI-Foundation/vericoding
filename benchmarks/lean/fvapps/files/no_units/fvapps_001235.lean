-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_house_positions (m n : Nat) : Nat := sorry

theorem count_house_positions_mod (m n : Nat) 
  (h1 : m ≥ 2) (h2 : n ≥ 2) : 
  count_house_positions m n < 1000000007 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_house_positions_symmetric (m n : Nat)
  (h1 : m ≥ 2) (h2 : n ≥ 2) :
  count_house_positions m n = count_house_positions n m := sorry

theorem count_house_positions_nonneg (m n : Nat)
  (h1 : m ≥ 2) (h2 : n ≥ 2) :
  count_house_positions m n ≥ 0 := sorry

theorem square_grid_nonzero (n : Nat) (h : n ≥ 2) :
  count_house_positions n n > 0 := sorry

theorem square_grid_monotone (n : Nat) (h : n ≥ 2) :
  count_house_positions (n+1) (n+1) > count_house_positions n n := sorry
-- </vc-theorems>