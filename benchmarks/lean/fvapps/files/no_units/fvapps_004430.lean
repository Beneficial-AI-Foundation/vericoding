-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_hollow (arr : List Int) : Bool := sorry

theorem invalid_hollow_not_enough_zeros {arr : List Int} :
  (arr.filter (λ x => x = 0)).length < 3 → ¬(is_hollow arr) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_hollow_nonzeros_between_zeros {arr : List Int} :
  (∃ i j k, i < j ∧ j < k ∧ 
   arr.get! i = 0 ∧ arr.get! k = 0 ∧ arr.get! j ≠ 0) → 
  ¬(is_hollow arr) := sorry

theorem valid_hollow_construction {n left right : Int} {zeros : List Int} :
  n ≥ 3 → left ≠ 0 → right ≠ 0 → 
  zeros.all (λ x => x = 0) → zeros.length = n →
  is_hollow ([left] ++ zeros ++ [right]) := sorry
-- </vc-theorems>