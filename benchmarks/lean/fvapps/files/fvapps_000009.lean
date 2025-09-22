-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_alice_score (s : String) : Nat :=
  sorry

def countOnes (s : String) : Nat :=
  sorry

def sortByLengthDesc (ls : List String) : List String :=
  sorry

def getAlternateSum (ls : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_not_exceed_input_length
  (s : String) :
  count_alice_score s ≤ s.length :=
sorry

theorem result_nonnegative
  (s : String) :
  count_alice_score s ≥ 0 :=
sorry

theorem empty_or_zeros_returns_zero
  (s : String) :
  (s.isEmpty ∨ s.all (· = '0')) → count_alice_score s = 0 :=
sorry

theorem all_ones_full_score
  (s : String) :
  s.all (· = '1') →
  s.length > 0 →
  count_alice_score s = s.length :=
sorry
-- </vc-theorems>