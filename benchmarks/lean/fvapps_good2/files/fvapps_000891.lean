-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_min_pairs (n : Nat) (k : Int) (arr : List Int) : Int × Nat :=
  sorry

def count_pairs_with_diff (arr : List Int) (k : Int) (min_diff : Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_min_pairs_nonneg_diff (n : Nat) (k : Int) (arr : List Int)
  (h1: n ≥ 2) (h2: arr.length = n) :
  let (min_diff, _) := solve_min_pairs n k arr
  min_diff ≥ 0 := by
  sorry

theorem solve_min_pairs_positive_count (n : Nat) (k : Int) (arr : List Int)
  (h1: n ≥ 2) (h2: arr.length = n) :
  let (_, count) := solve_min_pairs n k arr
  count > 0 := by
  sorry

theorem solve_min_pairs_count_accurate (n : Nat) (k : Int) (arr : List Int)
  (h1: n ≥ 2) (h2: arr.length = n) :
  let (min_diff, count) := solve_min_pairs n k arr
  count_pairs_with_diff arr k min_diff = count := by
  sorry

theorem solve_min_pairs_minimal (n : Nat) (k : Int) (arr : List Int)
  (h1: n ≥ 2) (h2: arr.length = n) :
  let (min_diff, _) := solve_min_pairs n k arr
  ∀ i j, 0 ≤ i ∧ i < n ∧ j > i ∧ j < n →
    let diff := arr[i]! + arr[j]! - k
    if diff ≥ 0 then diff ≥ min_diff else -diff ≥ min_diff := by
  sorry

theorem solve_min_pairs_permutation_invariant (n : Nat) (k : Int) (arr1 arr2 : List Int)
  (h1: n ≥ 2) (h2: arr1.length = n) (h3: arr2.length = n)
  (h4: arr2.Perm arr1) :
  solve_min_pairs n k arr1 = solve_min_pairs n k arr2 := by
  sorry
-- </vc-theorems>