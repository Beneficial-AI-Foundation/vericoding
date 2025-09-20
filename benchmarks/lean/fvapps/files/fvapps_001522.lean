-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_unique_or_pairs (arr : List Nat) : String := sorry

theorem check_unique_or_pairs_returns_valid_response {arr : List Nat} :
  check_unique_or_pairs arr = "YES" ∨ check_unique_or_pairs arr = "NO" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem long_arrays_return_no {arr : List Nat} :
  arr.length > 62 → check_unique_or_pairs arr = "NO" := sorry

theorem yes_result_implies_unique_ors {arr : List Nat} {i j k l : Nat} : 
  arr.length ≤ 62 →
  check_unique_or_pairs arr = "YES" →
  i ≤ j → j < arr.length →
  k ≤ l → l < arr.length →
  (i,j) ≠ (k,l) →
  (List.range (j - i + 1)).foldl (λ acc idx ↦ acc ||| arr[i + idx]!) 0 ≠
  (List.range (l - k + 1)).foldl (λ acc idx ↦ acc ||| arr[k + idx]!) 0 := sorry

theorem check_unique_or_pairs_deterministic {arr : List Nat} :
  check_unique_or_pairs arr = check_unique_or_pairs arr := sorry

theorem check_unique_or_pairs_order_invariant {arr : List Nat} :
  check_unique_or_pairs arr = check_unique_or_pairs arr.reverse := sorry
-- </vc-theorems>