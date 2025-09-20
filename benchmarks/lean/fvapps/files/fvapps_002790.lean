-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_cows (n: Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_cows_positive_integers {n: Int} (h: 1 ≤ n ∧ n ≤ 20) : 
  count_cows n > 0 :=
  sorry

theorem count_cows_non_positive {n: Int} (h: n ≤ 0) :
  count_cows n = 1 :=
  sorry

theorem count_cows_sequence {n: Int} (h: n ≥ 3) :
  count_cows n = count_cows (n-1) + count_cows (n-3) :=
  sorry
-- </vc-theorems>