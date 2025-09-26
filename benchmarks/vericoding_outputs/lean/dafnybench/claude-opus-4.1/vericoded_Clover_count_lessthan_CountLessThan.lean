import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this simple implementation
-- </vc-helpers>

-- <vc-definitions>
def CountLessThan (numbers : List Int) (threshold : Int) : Int :=
(numbers.filter (fun i => i < threshold)).length
-- </vc-definitions>

-- <vc-theorems>
theorem CountLessThan_spec (numbers : List Int) (threshold : Int) :
CountLessThan numbers threshold =
(numbers.filter (fun i => i < threshold)).length :=
by rfl
-- </vc-theorems>
