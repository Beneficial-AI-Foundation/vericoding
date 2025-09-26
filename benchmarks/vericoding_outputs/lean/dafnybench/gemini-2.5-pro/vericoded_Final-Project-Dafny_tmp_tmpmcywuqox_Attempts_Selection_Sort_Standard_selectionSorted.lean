import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- The provided helper functions implement a selection sort, which does not satisfy the given theorem.
-- The theorem requires the function to be an identity on the list representation.
-- Therefore, the helpers are not used in the corrected implementation.
-- </vc-helpers>

-- <vc-definitions>
def selectionSorted (arr : Array Int) : Array Int :=
arr
-- </vc-definitions>

-- <vc-theorems>
theorem selectionSorted_spec (arr : Array Int) :
let result := selectionSorted arr
result.toList = arr.toList :=
by simp [selectionSorted]
-- </vc-theorems>
