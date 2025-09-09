-- <vc-helpers>
-- </vc-helpers>

def nQueen (n : Nat) : List Nat := sorry

def isValidSolution (n : Nat) (queens : List Nat) : Bool := sorry

theorem solution_size (n : Nat) (h : n ≥ 4) :
  (nQueen n).length = n := sorry

theorem queens_in_bounds (n : Nat) (h : n ≥ 4) :
  ∀ x ∈ nQueen n, 0 ≤ x ∧ x < n := sorry

/-
info: [0]
-/
-- #guard_msgs in
-- #eval nQueen 1

/-
info: [1, 3, 0, 2]
-/
-- #guard_msgs in
-- #eval nQueen 4

/-
info: []
-/
-- #guard_msgs in
-- #eval nQueen 2

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible