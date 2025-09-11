-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumTriangularNumbers (n : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_triangular_negative_returns_zero {n : Int}
  (h : n ≤ 0) : sumTriangularNumbers n = 0 := sorry

theorem sum_triangular_positive_properties {n : Int} 
  (h : n > 0) : 
  sumTriangularNumbers n > 0 ∧ 
  sumTriangularNumbers n = n * (n + 1) * (n + 2) / 6 := sorry

theorem sum_triangular_increasing {n : Int}
  (h : n > 1) : sumTriangularNumbers n > sumTriangularNumbers (n-1) := sorry

/-
info: 20
-/
-- #guard_msgs in
-- #eval sum_triangular_numbers 4

/-
info: 56
-/
-- #guard_msgs in
-- #eval sum_triangular_numbers 6

/-
info: 0
-/
-- #guard_msgs in
-- #eval sum_triangular_numbers -3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded