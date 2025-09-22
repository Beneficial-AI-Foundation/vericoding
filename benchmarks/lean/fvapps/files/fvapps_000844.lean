-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_beautiful_subarrays (n k : Nat) (arr : List Nat) : Nat :=
  sorry

def is_valid_array (arr : List Nat) (n : Nat) : Bool :=
  sorry

def list_sorted (arr : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_bounds (n k : Nat) (arr : List Nat) :
  1 ≤ n ∧ n ≤ 100 ∧
  1 ≤ k ∧ k ≤ 100 ∧
  arr.length = n ∧
  (∀ x ∈ arr, 1 ≤ x ∧ x ≤ 2000) →
  0 ≤ count_beautiful_subarrays n k arr :=
sorry

theorem single_element_arrays (n k : Nat) :
  1 ≤ n ∧ n ≤ 10 ∧
  1 ≤ k ∧ k ≤ 10 →
  n ≤ count_beautiful_subarrays n k (List.replicate n 1) :=
sorry

theorem sorted_vs_unsorted (n k : Nat) (arr : List Nat) :
  1 ≤ n ∧ n ≤ 10 ∧
  1 ≤ k ∧ k ≤ 10 ∧
  is_valid_array arr n →
  count_beautiful_subarrays n k (list_sorted arr) = count_beautiful_subarrays n k arr :=
sorry

theorem minimal_case (k : Nat) :
  1 ≤ k ∧ k ≤ 10 →
  count_beautiful_subarrays 1 k [1] = 1 :=
sorry
-- </vc-theorems>