-- <vc-helpers>
-- </vc-helpers>

def two_by_n (n : Nat) (k : Nat) : Nat := sorry

theorem two_by_n_bounds (n k : Nat) (hn : n ≥ 1) (hk : k ≥ 1) :
  two_by_n n k < 12345787 := sorry

theorem two_by_n_single_color (n : Nat) (hn : n ≥ 1) :
  two_by_n n 1 = if n = 1 then 1 else 0 := sorry

theorem two_by_n_impossible (n : Nat) (k : Nat) (hn : n > 1) (hk : k ≤ 1) :
  two_by_n n k = 0 := sorry

theorem two_by_n_exists_solution (n k : Nat) (hn : n ≥ 1) (hk : k ≥ 2) :
  two_by_n n k > 0 := sorry

theorem two_by_n_deterministic (n : Nat) (k : Nat) (hn : n ≥ 1) (hk : k ≥ 1) :
  two_by_n n k = two_by_n n k := sorry

theorem two_by_n_min_colors (n : Nat) (hn : n > 1) :
  two_by_n n 2 > 0 := sorry

theorem two_by_n_monotonic (k : Nat) (hk : k ≥ 2) :
  two_by_n 1 k ≤ two_by_n 2 k := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval two_by_n 1 1

/-
info: 4
-/
-- #guard_msgs in
-- #eval two_by_n 4 2

/-
info: 168
-/
-- #guard_msgs in
-- #eval two_by_n 5 3

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible