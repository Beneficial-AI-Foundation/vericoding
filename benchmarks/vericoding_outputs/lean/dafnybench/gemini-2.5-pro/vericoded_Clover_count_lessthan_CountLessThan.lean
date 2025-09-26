import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def CountLessThan (numbers : List Int) (threshold : Int) : Int :=
match numbers with
  | [] => 0
  | head :: tail =>
    if head < threshold then
      1 + CountLessThan tail threshold
    else
      CountLessThan tail threshold
-- </vc-definitions>

-- <vc-theorems>
theorem CountLessThan_spec (numbers : List Int) (threshold : Int) :
CountLessThan numbers threshold =
(numbers.filter (fun i => i < threshold)).length :=
by
  induction numbers with
  | nil => simp [CountLessThan]
  | cons head tail ih =>
    simp [CountLessThan]
    split_ifs <;> simp [*, ih, Int.add_comm]
-- </vc-theorems>
