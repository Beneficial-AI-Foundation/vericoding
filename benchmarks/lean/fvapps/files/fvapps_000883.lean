-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_triangle_height (n : Nat) : Nat := sorry

theorem max_triangle_height_non_negative (n : Nat) :
  max_triangle_height n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_triangle_height_triangular (n : Nat) :
  (max_triangle_height n * (max_triangle_height n + 1)) / 2 ≤ n := sorry

theorem max_triangle_height_optimal (n : Nat) :
  let h := max_triangle_height n
  ((h + 1) * (h + 2)) / 2 > n ∨ h = n := sorry
-- </vc-theorems>