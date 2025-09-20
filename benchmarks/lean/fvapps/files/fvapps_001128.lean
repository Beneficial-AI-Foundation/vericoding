-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_subarrays_with_min (arr : List Int) (k : Int) : Nat :=
  sorry

def list_min (arr : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_subarrays_nonneg {arr : List Int} {k : Int}
  (h1 : arr ≠ []) :
  count_subarrays_with_min arr k ≥ 0 :=
sorry

theorem count_subarrays_less_than_min {arr : List Int} {k : Int}
  (h1 : arr ≠ [])
  (h2 : k < list_min arr) :
  count_subarrays_with_min arr k = 0 :=
sorry

theorem count_subarrays_equals_min {arr : List Int} {k : Int}
  (h1 : arr ≠ [])
  (h2 : k = list_min arr) :
  count_subarrays_with_min arr k ≥ arr.length :=
sorry

theorem count_subarrays_single_elem {arr : List Int} {k : Int}
  (h1 : arr.length = 1) :
  count_subarrays_with_min arr k = if arr.head! = k then 1 else 0 :=
sorry

theorem count_subarrays_identical_elems {arr : List Int} {k : Int}
  (h1 : arr ≠ [])
  (h2 : ∀ x ∈ arr, x = k) :
  count_subarrays_with_min arr k = (arr.length * (arr.length + 1)) / 2 :=
sorry

theorem count_subarrays_monotonic {arr : List Int} {k : Int}
  (h1 : arr ≠ [])
  (h2 : ∀ x ∈ arr, x > 0) :
  count_subarrays_with_min arr k ≥ count_subarrays_with_min arr (k+1) :=
sorry
-- </vc-theorems>