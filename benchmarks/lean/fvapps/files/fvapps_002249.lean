-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_multisets (n k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_multisets_result_bounds (n k : Nat) 
  (h1 : n > 0) (h2 : k ≤ n) : 
  count_multisets n k < 998244353 ∧ count_multisets n k ≥ 0 :=
  sorry

theorem count_multisets_k_equal_n (n k : Nat)
  (h1 : n > 0) (h2 : k = n) :
  count_multisets n k > 0 :=
  sorry

theorem count_multisets_known_values_1 :
  count_multisets 4 2 = 2 :=
  sorry

theorem count_multisets_known_values_2 :
  count_multisets 2525 425 = 687232272 :=
  sorry

theorem count_multisets_known_values_3 :
  count_multisets 3000 1 = 815951975 :=
  sorry
-- </vc-theorems>