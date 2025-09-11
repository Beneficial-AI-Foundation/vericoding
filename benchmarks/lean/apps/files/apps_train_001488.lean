-- <vc-preamble>
def solve_atoms (input : List (Nat × Nat) × List Nat) : List Nat := sorry

variable (n : Nat)

def empty_case (n : Nat) : List (Nat × Nat) × List Nat := 
  ([(n, 1)], [0])
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def all_case (n : Nat) : List (Nat × Nat) × List Nat :=
  ([(n, 1)], n :: List.range n)
-- </vc-definitions>

-- <vc-theorems>
theorem solve_atoms_empty_groups (h : n > 0) :
  solve_atoms (empty_case n) = List.replicate n 1 := sorry

theorem solve_atoms_all_groups (h : n > 0) :
  solve_atoms (all_case n) = List.replicate n 1 := sorry

/-
info: [3]
-/
-- #guard_msgs in
-- #eval solve_atoms [case1]

/-
info: [4]
-/
-- #guard_msgs in
-- #eval solve_atoms [case2]

/-
info: [3, 4]
-/
-- #guard_msgs in
-- #eval solve_atoms [case1, case2]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded