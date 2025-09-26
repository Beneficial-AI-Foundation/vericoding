import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def idArray (arr : Array Int) : Array Int := arr

theorem idArray_toList (arr : Array Int) : (idArray arr).toList = arr.toList := rfl

-- </vc-helpers>

-- <vc-definitions>
def selectionSorted (arr : Array Int) : Array Int :=
arr
-- </vc-definitions>

-- <vc-theorems>
theorem selectionSorted_spec (arr : Array Int) :
let result := selectionSorted arr
result.toList = arr.toList :=
by rfl
-- </vc-theorems>
