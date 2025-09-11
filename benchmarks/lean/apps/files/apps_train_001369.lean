-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_interleavings (n m k : Nat) (A B : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_interleavings_minimal_valid :
  count_interleavings 1 1 1 [1] [1] ≥ 0 :=
sorry

theorem count_interleavings_same_numbers :
  count_interleavings 2 2 1 [1, 1] [1, 1] ≥ 0 :=
sorry

theorem count_interleavings_different_numbers :
  count_interleavings 2 2 4 [1, 2] [3, 4] ≥ 0 :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_interleavings 2 2 4 [1, 3] [3, 4]

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_interleavings 2 2 3 [1, 3] [3, 4]

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_interleavings 2 2 4 [4, 7] [8, 5]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible