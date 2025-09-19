-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def number_of_pairs (gloves : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pairs_non_negative (gloves : List String) :
  number_of_pairs gloves ≥ 0 :=
sorry

theorem pairs_at_most_half (gloves : List String) :
  number_of_pairs gloves ≤ gloves.length / 2 :=
sorry

theorem empty_list_zero : 
  number_of_pairs [] = 0 :=
sorry

theorem duplicate_list_pairs (gloves : List String) :
  number_of_pairs (gloves ++ gloves) = gloves.length :=
sorry
-- </vc-theorems>