-- <vc-preamble>
def list_max : List Int → Int
  | [] => 0
  | (x::xs) => max x (list_max xs)

def list_min : List Int → Int
  | [] => 0
  | (x::xs) => min x (list_min xs)

def list_sum : List Int → Int
  | [] => 0
  | (x::xs) => x + list_sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_subarrays (arr : List Int) : List (List Int) := sorry

def find_max_subarray_sum (arr : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
def subarray_sums (arr : List Int) : List Int :=
  (get_subarrays arr).map list_sum

theorem max_subarray_sum_at_least_one_element {arr : List Int} (h : arr ≠ []) :
  find_max_subarray_sum arr ≥ list_max arr :=
sorry

theorem max_subarray_sum_positive_only {arr : List Int} (h : arr ≠ [])
  (h_pos : ∀ x ∈ arr, x ≥ 0) :
  find_max_subarray_sum arr ≥ list_sum arr :=
sorry

theorem max_subarray_sum_empty_and_nonempty (arr : List Int) :
  (arr = [] → find_max_subarray_sum arr = 0) ∧
  (arr ≠ [] → find_max_subarray_sum arr ≥ list_min arr) :=
sorry

theorem max_subarray_contiguous {arr : List Int} (h : arr ≠ []) :
  find_max_subarray_sum arr = list_max (subarray_sums arr) :=
sorry

theorem max_subarray_base_cases :
  find_max_subarray_sum [] = 0 ∧
  find_max_subarray_sum [0] = 0 :=
sorry
-- </vc-theorems>