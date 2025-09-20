-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_qaq_subsequences (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_qaq_subsequences_nonnegative (s : String) :
  count_qaq_subsequences s ≥ 0 :=
  sorry

theorem count_qaq_subsequences_lt_two_q (s : String) :
  (s.data.filter (· = 'Q')).length < 2 →
  count_qaq_subsequences s = 0 :=
  sorry
-- </vc-theorems>