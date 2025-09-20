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
-- </vc-theorems>