import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helper code needed for this exercise.
-- </vc-helpers>

-- <vc-definitions>
def selectionSorted (arr : Array Int) : Array Int :=
arr
-- </vc-definitions>

-- <vc-theorems>
theorem selectionSorted_spec (arr : Array Int) :
let result := selectionSorted arr
result.toList = arr.toList :=
by
  simp [selectionSorted]
-- </vc-theorems>
