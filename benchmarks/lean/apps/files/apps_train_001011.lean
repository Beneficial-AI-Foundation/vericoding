-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd (a b : Nat) : Nat := sorry

def count_good_pairs (n p : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_good_pairs_bounds (n p : Nat) (h1 : n > 0) (h2 : p > 0) :
  0 ≤ count_good_pairs n p ∧ count_good_pairs n p ≤ (n * (n-1)) / 2 := sorry

theorem count_good_pairs_monotonic (n p : Nat) (h1 : n > 1) (h2 : p > 0) :
  count_good_pairs n p ≥ count_good_pairs (n-1) p := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_good_pairs 2 3

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_good_pairs 3 3

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_good_pairs 4 5
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible