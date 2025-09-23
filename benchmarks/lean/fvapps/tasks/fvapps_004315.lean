-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rankings (arr : List Int) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rankings_length {arr : List Int} (h : arr ≠ []) :
  (rankings arr).length = arr.length :=
sorry

theorem rankings_range {arr : List Int} (h : arr ≠ []) :
  let ranks := rankings arr 
  (∀ r ∈ ranks, 1 ≤ r ∧ r ≤ arr.length) ∧ 
  (ranks.length = arr.length) :=
sorry
-- </vc-theorems>