import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed
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
  simp only [CountLists]
  constructor
  · -- count ≥ 0
    exact Int.ofNat_nonneg lists.size
  · -- count = lists.size (as Int)
    rfl
-- </vc-theorems>
