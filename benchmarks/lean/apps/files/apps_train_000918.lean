-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_packaging 2

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_packaging 5

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_packaging 7
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible