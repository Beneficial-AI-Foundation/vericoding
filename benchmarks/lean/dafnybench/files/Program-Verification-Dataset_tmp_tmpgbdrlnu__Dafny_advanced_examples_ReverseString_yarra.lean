-- <vc-preamble>
def reversed (arr : Array Char) (outarr : Array Char) : Prop :=
arr.size = outarr.size ∧
∀ k, 0 ≤ k ∧ k ≤ arr.size - 1 →
outarr[k]! = arr[arr.size - 1 - k]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def yarra (arr : Array Char) : Array Char :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem yarra_spec (arr : Array Char) :
arr.size > 0 →
let outarr := yarra arr
outarr.size = arr.size ∧ reversed arr outarr :=
sorry
-- </vc-theorems>