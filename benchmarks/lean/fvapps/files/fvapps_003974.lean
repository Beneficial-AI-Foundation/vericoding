-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pairwise_pairs : List Int → Int → List (Int × Int)
| xs, n =>
sorry

def pairwise : List Int → Int → Int
| xs, n =>
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pairwise_nonnegative {arr : List Int} {n : Int} :
  pairwise arr n ≥ 0 := by
sorry

theorem pairwise_less_than_triangular {arr : List Int} {n : Int} :
  let max_triangular := (arr.length * (arr.length - 1)) / 2
  pairwise arr n ≤ max_triangular := by
sorry

theorem pairwise_indices_sum_correctly {arr : List Int} {n : Int} :
  let used_indices := List.map Prod.fst (pairwise_pairs arr n) ++ List.map Prod.snd (pairwise_pairs arr n)
  List.foldr (· + ·) 0 used_indices = pairwise arr n := by
sorry

theorem pairwise_indices_unique {arr : List Int} {n : Int} :
  let indices := List.map Prod.fst (pairwise_pairs arr n) ++ List.map Prod.snd (pairwise_pairs arr n)
  List.Nodup indices := by
sorry

theorem pairwise_empty_zero {n : Int} :
  pairwise [] n = 0 := by
sorry
-- </vc-theorems>