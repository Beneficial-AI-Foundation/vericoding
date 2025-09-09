-- <vc-helpers>
-- </vc-helpers>

def max_doggo_paths (n: Nat) : Nat :=
  sorry

theorem max_doggo_paths_nonneg (n: Nat) : 
  max_doggo_paths n ≥ 0 :=
sorry

theorem max_doggo_paths_less_than_input {n: Nat} (h: n > 1) :
  max_doggo_paths n < n :=
sorry

theorem max_doggo_paths_one :
  max_doggo_paths 1 = 0 :=
sorry

theorem max_doggo_paths_monotone {n: Nat} (h: n ≥ 2) :
  max_doggo_paths n ≥ max_doggo_paths (n-1) :=
sorry

theorem max_doggo_paths_three :
  max_doggo_paths 3 = 1 :=
sorry

theorem max_doggo_paths_six :
  max_doggo_paths 6 = 3 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_doggo_paths 4

/-
info: 6
-/
-- #guard_msgs in
-- #eval max_doggo_paths 10

/-
info: 0
-/
-- #guard_msgs in
-- #eval max_doggo_paths 1

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible