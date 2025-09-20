-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def select_subarray (arr : List Int) : Nat × Int :=
  sorry

def get_ratio (arr : List Int) (idx : Nat) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem select_subarray_index_bounds {arr : List Int}
  (h_size : arr.length ≥ 2)
  (h_nonzero : ∀ x ∈ arr, x ≠ 0) :
  (select_subarray arr).1 < arr.length := by
  sorry

theorem select_subarray_matches_input {arr : List Int}
  (h_size : arr.length ≥ 2)
  (h_nonzero : ∀ x ∈ arr, x ≠ 0) :
  (select_subarray arr).2 = arr[(select_subarray arr).1]! := by
  sorry

theorem select_subarray_minimum_ratio {arr : List Int}
  (h_size : arr.length ≥ 2)
  (h_nonzero : ∀ x ∈ arr, x ≠ 0) :
  ∀ i < arr.length,
    get_ratio arr (select_subarray arr).1 ≤ get_ratio arr i := by
  sorry
-- </vc-theorems>