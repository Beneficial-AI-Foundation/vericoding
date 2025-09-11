-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unique_paths (m n : Nat) : Nat := sorry

theorem unique_paths_positive (m n : Nat) (h1 : m > 0) (h2 : n > 0) :
  unique_paths m n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unique_paths_symmetry (m n : Nat) :
  unique_paths m n = unique_paths n m := sorry

theorem unique_paths_single_row (n : Nat) (h : n > 0) :
  unique_paths 1 n = 1 := sorry

theorem unique_paths_single_col (n : Nat) (h : n > 0) :
  unique_paths n 1 = 1 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval unique_paths 3 2

/-
info: 28
-/
-- #guard_msgs in
-- #eval unique_paths 7 3

/-
info: 28
-/
-- #guard_msgs in
-- #eval unique_paths 3 7
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible