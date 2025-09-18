-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.isSubsetOf (l1 l2 : List α) [BEq α] : Bool :=
  sorry

def people_indexes (favorite_companies : List (List String)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem people_indexes_valid_indices
  (favorite_companies : List (List String)) :
  let result := people_indexes favorite_companies
  ∀ i ∈ result, i < favorite_companies.length :=
sorry

theorem people_indexes_empty :
  people_indexes [] = [] :=
sorry
-- </vc-theorems>