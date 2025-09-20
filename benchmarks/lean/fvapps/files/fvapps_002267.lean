-- <vc-preamble>
def isSorted (arr : List Int) : Prop :=
  ∀ i j, i < j → j < arr.length → arr[i]! ≤ arr[j]!

def isStrictlySorted (arr : List Int) : Prop :=
  ∀ i j, i < j → j < arr.length → arr[i]! < arr[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minimum_operations (arr : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_bounds (arr : List Int) (h : arr ≠ []) :
  0 ≤ minimum_operations arr ∧ minimum_operations arr ≤ arr.length :=
sorry

theorem sorted_unique_needs_zero {arr : List Int} (h1 : arr ≠ [])
  (h2 : isStrictlySorted arr) :
  minimum_operations arr = 0 :=
sorry
-- </vc-theorems>