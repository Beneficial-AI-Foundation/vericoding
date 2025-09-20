-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_max_subseq_sum (n : Nat) (arr : List Int) : Int × Nat × List Nat := sorry

theorem output_format_types {n : Nat} {arr : List Int} (h : arr.length > 0) :
  let (sum_val, k, indices) := solve_max_subseq_sum n arr
  indices.all (fun i => i ≥ 0) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_negative_returns_zeros {n : Nat} {arr : List Int} 
  (h₁ : arr.length > 0)
  (h₂ : ∀ x ∈ arr, x < 0) :
  let (sum_val, k, indices) := solve_max_subseq_sum n arr
  sum_val = 0 ∧ k = 0 ∧ indices = [] := sorry

theorem indices_in_bounds {n : Nat} {arr : List Int} (h : arr.length > 0) :
  let (_, _, indices) := solve_max_subseq_sum n arr
  (∀ i ∈ indices, 0 ≤ i ∧ i < n) ∧ 
  indices.Nodup := sorry 

theorem return_sum_matches_indices {n : Nat} {arr : List Int} (h : arr.length > 0) :
  let (sum_val, k, indices) := solve_max_subseq_sum n arr
  (indices ≠ [] → k = indices.length) ∧
  (indices = [] → sum_val = 0 ∧ k = 0) := sorry
-- </vc-theorems>