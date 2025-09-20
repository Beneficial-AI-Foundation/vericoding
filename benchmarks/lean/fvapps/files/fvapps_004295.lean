-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def consonant_count (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem consonant_count_nonnegative (s : String) :
  consonant_count s ≥ 0 :=
sorry

theorem consonant_count_bounded (s : String) :
  consonant_count s ≤ s.length :=
sorry

theorem consonant_count_empty :
  consonant_count "" = 0 :=
sorry 

theorem consonant_count_case_insensitive (s : String) :
  consonant_count s = consonant_count s.toUpper ∧ 
  consonant_count s = consonant_count s.toLower :=
sorry
-- </vc-theorems>