import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No helper definitions are required for this problem.
-- </vc-helpers>

-- <vc-definitions>
def CountLists (lists : Array (Array Int)) : Int :=
Int.ofNat lists.size
-- </vc-definitions>

-- <vc-theorems>
theorem CountLists_spec (lists : Array (Array Int)) :
let count := CountLists lists
count ≥ 0 ∧ count = lists.size :=
by
  simp [CountLists]
-- </vc-theorems>
