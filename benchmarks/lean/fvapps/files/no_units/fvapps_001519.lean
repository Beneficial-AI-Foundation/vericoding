-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_rubiks_cuboid (m n o : Nat) : Nat := sorry

theorem solve_non_negative (m n o : Nat) : 
  solve_rubiks_cuboid m n o ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_commutative (m n o : Nat) :
  solve_rubiks_cuboid m n o = solve_rubiks_cuboid m o n ∧
  solve_rubiks_cuboid m n o = solve_rubiks_cuboid n m o ∧ 
  solve_rubiks_cuboid m n o = solve_rubiks_cuboid n o m ∧
  solve_rubiks_cuboid m n o = solve_rubiks_cuboid o m n ∧
  solve_rubiks_cuboid m n o = solve_rubiks_cuboid o n m := sorry

theorem small_cubes_zero (m n o : Nat) :
  m ≤ 2 → n ≤ 2 → o ≤ 2 → solve_rubiks_cuboid m n o = 0 := sorry

theorem increases_with_size (m n o : Nat) :
  solve_rubiks_cuboid (m + 1) n o ≥ solve_rubiks_cuboid m n o ∧
  solve_rubiks_cuboid m (n + 1) o ≥ solve_rubiks_cuboid m n o ∧
  solve_rubiks_cuboid m n (o + 1) ≥ solve_rubiks_cuboid m n o := sorry
-- </vc-theorems>