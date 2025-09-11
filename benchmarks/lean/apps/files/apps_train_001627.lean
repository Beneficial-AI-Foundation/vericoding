-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Family := List (List Nat)

def find_extended_family (n k : Nat) (families : Family) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem always_includes_first_family {n k : Nat} {families : Family} :
  1 ≤ find_extended_family n k families := by
  sorry

theorem result_within_bounds {n k : Nat} {families : Family} :
  1 ≤ find_extended_family n k families ∧ find_extended_family n k families ≤ n := by
  sorry

theorem increasing_k_decreases_relatives {n k : Nat} {families : Family} :
  k < 10 → find_extended_family n k families ≥ find_extended_family n (k+1) families := by
  sorry

theorem output_is_nat {n k : Nat} {families : Family} :
  find_extended_family n k families = find_extended_family n k families := by
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_extended_family 4 2 ["4 4 6 7 8", "4 8 3 0 4", "2 0 10", "6 1 2 3 0 5 8"]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_extended_family 3 1 ["2 1 2", "2 2 3", "2 3 4"]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_extended_family 2 2 ["3 1 2 3", "3 4 5 6"]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded