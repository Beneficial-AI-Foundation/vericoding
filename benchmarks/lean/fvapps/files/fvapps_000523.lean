-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def total_variation_count (n : Nat) (k : Nat) (sequence : List Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem total_variation_nonNegative {n k : Nat} {sequence : List Int} :
  total_variation_count n k sequence ≥ 0 :=
sorry

theorem total_variation_upperBound {n k : Nat} {sequence : List Int} :
  sequence.length = n →
  total_variation_count n k sequence ≤ (n * (n-1)) / 2 :=
sorry

theorem total_variation_zeroK {n : Nat} {sequence : List Int} :
  sequence.length = n →
  total_variation_count n 0 sequence = 
    (List.range n).foldl (fun acc i => 
      acc + (List.range (n-i-1)).foldl (fun acc' j =>
        acc' + if sequence.get! i ≠ sequence.get! (i+j+1) then 1 else 0) 0) 0 :=
sorry

theorem total_variation_permutation {n k : Nat} {sequence : List Int} :
  sequence.length = n →
  ∀ perm : List Int, List.Perm sequence perm →
  total_variation_count n k sequence = total_variation_count n k perm :=
sorry

theorem total_variation_symmetry {n k : Nat} {sequence : List Int} :
  sequence.length = n →
  total_variation_count n k sequence = total_variation_count n k sequence.reverse :=
sorry
-- </vc-theorems>