-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_sad_guests (n k : Nat) (fav_pairs : List (Nat × Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_sad_guests_single_person {k : Nat} (h : k ≥ 1) :
  min_sad_guests 1 k [] = k :=
sorry

theorem min_sad_guests_empty_pairs {n k : Nat} (h1 : n ≥ 1) (h2 : k ≥ 1) :
  min_sad_guests n k [] = k :=
sorry

theorem min_sad_guests_edge_cases_1 :
  min_sad_guests 1 1 [] = 1 :=
sorry

theorem min_sad_guests_edge_cases_2 :
  min_sad_guests 2 1 [(1,2)] = 0 :=
sorry

theorem min_sad_guests_edge_cases_3 :
  min_sad_guests 3 2 [(1,2), (2,3)] = 0 :=
sorry
-- </vc-theorems>