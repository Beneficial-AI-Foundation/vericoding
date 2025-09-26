import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def CountLists (lists : Array (Array Int)) : Int :=
 (lists.size : Int) 
-- </vc-definitions>

-- <vc-theorems>
theorem CountLists_spec (lists : Array (Array Int)) :
let count := CountLists lists
count ≥ 0 ∧ count = lists.size :=
 by apply And.intro (Nat.cast_nonneg _) rfl 
-- </vc-theorems>
