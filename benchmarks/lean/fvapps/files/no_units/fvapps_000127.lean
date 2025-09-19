-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_score_sightseeing_pair (values: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_score_basic_case (values: List Nat) :
  values = [8,1,5,2,6] → max_score_sightseeing_pair values = 11 :=
  sorry

theorem max_score_min_case (values: List Nat) :
  values = [1,2] → max_score_sightseeing_pair values = 2 :=
  sorry

theorem max_score_equal_values (values: List Nat) :
  values = [5,5,5,5] → max_score_sightseeing_pair values = 9 :=
  sorry

theorem max_score_two_ones (values: List Nat) :
  values = [1,1] → max_score_sightseeing_pair values = 1 :=
  sorry
-- </vc-theorems>