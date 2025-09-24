-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CountLists (lists : Array (Array Int)) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem CountLists_spec (lists : Array (Array Int)) :
let count := CountLists lists
count ≥ 0 ∧ count = lists.size :=
sorry
-- </vc-theorems>