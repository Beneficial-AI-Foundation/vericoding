-- <vc-helpers>
-- </vc-helpers>

def count_pairs_int (d : Nat) (m : Nat) : Nat := sorry

theorem count_pairs_int_non_negative (d m : Nat) (h : d > 0) (h2 : m > 1) :
  (count_pairs_int d m) ≥ 0 := sorry

theorem count_pairs_int_zero_when_d_large (d m : Nat) (h : d > 0) (h2 : m > 1) (h3 : d ≥ m-1) :
  count_pairs_int d m = 0 := sorry

theorem count_pairs_int_upper_bound (d m : Nat) (h : d > 0) (h2 : m > 1) :
  count_pairs_int d m ≤ max 0 (m-d-1) := sorry

theorem count_pairs_int_small_m (d : Nat) (h : d > 0) :
  count_pairs_int d (d+1) = 0 ∧ count_pairs_int d d = 0 := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval count_pairs_int 1 50

/-
info: 7
-/
-- #guard_msgs in
-- #eval count_pairs_int 3 100

/-
info: 86
-/
-- #guard_msgs in
-- #eval count_pairs_int 6 350

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible