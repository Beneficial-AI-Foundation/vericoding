-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Direction := String

def direction_in_grid (n m : Nat) : Direction :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem direction_in_grid_output_format {n m : Nat} (h1 : n > 0) (h2 : m > 0) (h3 : n ≤ 1000) (h4 : m ≤ 1000) :
  direction_in_grid n m = "U" ∨ 
  direction_in_grid n m = "D" ∨
  direction_in_grid n m = "L" ∨ 
  direction_in_grid n m = "R" :=
  sorry

theorem equal_dimensions_pattern {n : Nat} (h1 : n > 0) (h2 : n ≤ 1000) :
  direction_in_grid n n = (if n % 2 = 0 then "L" else "R") :=
  sorry

theorem dimension_comparison_consistency {n m : Nat} (h1 : n > 0) (h2 : m > 0) (h3 : n ≤ 1000) (h4 : m ≤ 1000) :
  (m ≥ n → direction_in_grid n m = "L" ∨ direction_in_grid n m = "R") ∧
  (m < n → direction_in_grid n m = "U" ∨ direction_in_grid n m = "D") :=
  sorry

/-
info: 'R'
-/
-- #guard_msgs in
-- #eval direction_in_grid 3 3

/-
info: 'L'
-/
-- #guard_msgs in
-- #eval direction_in_grid 2 4

/-
info: 'U'
-/
-- #guard_msgs in
-- #eval direction_in_grid 4 2
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded