-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_nonconsecutive_subsets (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_nonconsecutive_subsets_nonnegative (n : Nat) :
  count_nonconsecutive_subsets n ≥ 0 :=
  sorry

theorem count_nonconsecutive_subsets_monotonic (n : Nat) : 
  n > 0 → count_nonconsecutive_subsets n > count_nonconsecutive_subsets (n-1) :=
  sorry

theorem count_nonconsecutive_subsets_base_cases :
  count_nonconsecutive_subsets 0 = 0 ∧ count_nonconsecutive_subsets 1 = 1 :=
  sorry

/-
info: 12
-/
-- #guard_msgs in
-- #eval count_nonconsecutive_subsets 5

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_nonconsecutive_subsets 3

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_nonconsecutive_subsets 2
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible