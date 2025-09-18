-- <vc-preamble>
def total_fruit (tree : List Nat) : Nat := sorry

theorem total_fruit_bounds {tree : List Nat} (h : tree ≠ []) : 
  1 ≤ total_fruit tree ∧ total_fruit tree ≤ tree.length := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxSubseqLengthWithTwoTypes (tree : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem total_fruit_min_length {tree : List Nat} (h : tree.length ≥ 3) :
  total_fruit tree ≥ 2 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval total_fruit [1, 2, 1]

/-
info: 3
-/
-- #guard_msgs in
-- #eval total_fruit [0, 1, 2, 2]

/-
info: 4
-/
-- #guard_msgs in
-- #eval total_fruit [1, 2, 3, 2, 2]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible