-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_positives_sum_negatives (arr : List Int) : List Int := sorry

theorem count_positives (arr : List Int) :
  arr ≠ [] → 
  (count_positives_sum_negatives arr).get! 0 = 
    (arr.filter (fun x => x > 0)).length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_negatives (arr : List Int) :
  arr ≠ [] →
  (count_positives_sum_negatives arr).get! 1 = 
    (arr.filter (fun x => x < 0)).foldl (· + ·) 0 := sorry
-- </vc-theorems>