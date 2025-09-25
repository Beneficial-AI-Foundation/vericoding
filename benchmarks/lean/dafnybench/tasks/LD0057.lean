-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CountLessThan (numbers : List Int) (threshold : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem CountLessThan_spec (numbers : List Int) (threshold : Int) :
CountLessThan numbers threshold =
(numbers.filter (fun i => i < threshold)).length :=
sorry
-- </vc-theorems>