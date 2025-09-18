-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def number_ways (hats : List (List Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem number_ways_basic_cases1 :
  number_ways [[3,4], [4,5], [5]] = 1 :=
sorry

theorem number_ways_basic_cases2 :
  number_ways [[3,5,1], [3,5]] = 4 :=
sorry

theorem number_ways_empty :
  number_ways [] = 1 :=
sorry
-- </vc-theorems>