-- <vc-helpers>
-- </vc-helpers>

def max_score_sightseeing_pair (values: List Nat) : Nat :=
  sorry

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

/-
info: 11
-/
-- #guard_msgs in
-- #eval max_score_sightseeing_pair [8, 1, 5, 2, 6]

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_score_sightseeing_pair [1, 2]

/-
info: 9
-/
-- #guard_msgs in
-- #eval max_score_sightseeing_pair [5, 5, 5, 5]

-- Apps difficulty: interview
-- Assurance level: unguarded