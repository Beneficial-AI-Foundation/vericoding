-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_paths (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_paths_nonnegative (n : Nat) :
  count_paths n ≥ 0 ∧ count_paths n % 2 = 0 :=
sorry 

theorem count_paths_zero :
  count_paths 0 = 0 :=
sorry

theorem count_paths_monotonic {n : Nat} (h : n > 0) :
  count_paths n > count_paths (n-1) :=
sorry

theorem count_paths_superlinear {n : Nat} (h1 : n > 1) :
  count_paths n / count_paths (n-1) > 1 :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_paths 2

/-
info: 84
-/
-- #guard_msgs in
-- #eval count_paths 5

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_paths 0
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible