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
-- </vc-theorems>