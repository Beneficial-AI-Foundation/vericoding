def count_subarrays_with_min (arr : List Int) (k : Int) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def list_min (arr : List Int) : Int :=
  sorry

-- Result should never be negative

theorem count_subarrays_nonneg {arr : List Int} {k : Int} 
  (h1 : arr ≠ []) :
  count_subarrays_with_min arr k ≥ 0 :=
  sorry

-- If k is less than min(arr), result should be 0  

theorem count_subarrays_less_than_min {arr : List Int} {k : Int}
  (h1 : arr ≠ [])
  (h2 : k < list_min arr) :
  count_subarrays_with_min arr k = 0 :=
  sorry

-- If k equals min(arr), result should be at least length of array

theorem count_subarrays_equals_min {arr : List Int} {k : Int}
  (h1 : arr ≠ []) 
  (h2 : k = list_min arr) :
  count_subarrays_with_min arr k ≥ arr.length :=
  sorry

-- Single element array returns 1 if element equals k, 0 otherwise

theorem count_subarrays_single_elem {arr : List Int} {k : Int}
  (h1 : arr.length = 1) :
  count_subarrays_with_min arr k = if arr.head! = k then 1 else 0 :=
  sorry

-- For array of identical elements, result is n*(n+1)/2

theorem count_subarrays_identical_elems {arr : List Int} {k : Int}
  (h1 : arr ≠ [])
  (h2 : ∀ x ∈ arr, x = k) :
  count_subarrays_with_min arr k = (arr.length * (arr.length + 1)) / 2 :=
  sorry

-- For any k, result with k should be >= result with k+1

theorem count_subarrays_monotonic {arr : List Int} {k : Int}
  (h1 : arr ≠ [])
  (h2 : ∀ x ∈ arr, x > 0) :
  count_subarrays_with_min arr k ≥ count_subarrays_with_min arr (k+1) :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_subarrays_with_min [2, 2] 2

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_subarrays_with_min [3] 3

-- Apps difficulty: interview
-- Assurance level: guarded