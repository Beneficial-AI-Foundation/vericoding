-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_key_occurrences (arr : List Int) (key : Int) (queries : List Nat) : 
  List (Nat × Nat × Nat) := sorry

-- For each element in result, all components are natural numbers
-- </vc-definitions>

-- <vc-theorems>
theorem result_components_natural_numbers (arr : List Int) (key : Int) (queries : List Nat) :
  let result := find_key_occurrences arr key queries
  ∀ r ∈ result, r.1 ≥ 0 ∧ r.2.1 ≥ 0 ∧ r.2.2 ≥ 0 :=
sorry

-- Result length matches queries length 

theorem result_length_matches_queries (arr : List Int) (key : Int) (queries : List Nat) :
  let result := find_key_occurrences arr key queries
  result.length = queries.length :=
sorry

-- For monotonically increasing queries, occurrences are monotonically decreasing

theorem monotonic_occurrences (arr : List Int) (key : Int) (queries : List Nat) :
  let result := find_key_occurrences arr key queries
  ∀ i j, i < j → j < queries.length → queries.get! i < queries.get! j → 
    (result.get! i).1 ≥ (result.get! j).1 :=
sorry

-- Second component equals array length minus query index

theorem brute_force_counts (arr : List Int) (key : Int) (queries : List Nat) :
  let result := find_key_occurrences arr key queries
  ∀ i, i < queries.length → 
    (result.get! i).2.1 = arr.length - queries.get! i :=
sorry

-- Third component is at least 1

theorem dp_counts_positive (arr : List Int) (key : Int) (queries : List Nat) :
  let result := find_key_occurrences arr key queries
  ∀ r ∈ result, r.2.2 ≥ 1 :=
sorry

-- First component counts actual occurrences after query index

theorem occurrence_count_correct (arr : List Int) (key : Int) (queries : List Nat) :
  let result := find_key_occurrences arr key queries
  ∀ i, i < queries.length →
    (result.get! i).1 = ((arr.drop (queries.get! i)).filter (· = key)).length :=
sorry
-- </vc-theorems>