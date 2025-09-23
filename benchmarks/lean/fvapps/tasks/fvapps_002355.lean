-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numEquivDominoPairs (dominoes : List (List Nat)) : Nat := sorry

theorem output_non_negative 
  (dominoes : List (List Nat)) :
  numEquivDominoPairs dominoes ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_arrays_handled
  (dominoes : List (List Nat)) :
  numEquivDominoPairs (dominoes ++ [[]]) ≥ numEquivDominoPairs dominoes := sorry

theorem identical_pairs_increase_count
  (dominoes : List (List Nat))
  (h : dominoes ≠ [])
  (first : List Nat)
  (h2 : first ∈ dominoes) :
  numEquivDominoPairs (dominoes ++ [first]) ≥ numEquivDominoPairs dominoes := sorry
-- </vc-theorems>