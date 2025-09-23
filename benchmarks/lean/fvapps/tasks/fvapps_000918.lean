-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_packaging (n : Nat) : Nat := sorry

theorem package_size_formula {n : Nat} (h : n > 0) : 
  solve_packaging n = n / 2 + 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem package_size_positive {n : Nat} (h : n > 0) :
  solve_packaging n > 0 := sorry

theorem package_size_bounded {n : Nat} (h : n > 0) :
  solve_packaging n ≤ n := sorry

theorem package_size_maximizes_leftovers {n : Nat} (h : n > 0) :
  ∀ k : Nat, k > 0 → k < solve_packaging n → 
    n % k ≤ n % (solve_packaging n) := sorry
-- </vc-theorems>