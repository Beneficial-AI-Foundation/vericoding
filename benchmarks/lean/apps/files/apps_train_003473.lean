def choose (n m : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def count_paths (n: Nat) (start_pos: Nat × Nat) : Nat :=
  sorry

theorem count_paths_one_by_one {n: Nat} (h: n = 1) :
  count_paths n (0, 0) = 0 :=
  sorry

theorem count_paths_non_negative {n row col: Nat} (h1: row < n) (h2: col < n) (h3: n > 0) :
  count_paths n (row, col) ≥ 0 :=
  sorry

theorem count_paths_only_vertical {n row col: Nat} (h1: col = n - 1) (h2: row > 0) (h3: row < n) (h4: n > 0) :
  count_paths n (row, col) = 1 :=
  sorry

theorem count_paths_only_horizontal {n row col: Nat} (h1: row = 0) (h2: col < n - 1) (h3: n > 0) :
  count_paths n (row, col) = 1 :=
  sorry

theorem count_paths_start_equals_target {n: Nat} (h: n ≥ 2) :
  count_paths n (0, n-1) = 1 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_paths 1 (0, 0)

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_paths 2 (1, 0)

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_paths 3 (1, 0)

/-
info: 70
-/
-- #guard_msgs in
-- #eval count_paths 5 (4, 0)

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible