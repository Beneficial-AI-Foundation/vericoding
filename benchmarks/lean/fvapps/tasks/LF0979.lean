-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_running_patterns (n : Nat) (k : Nat) (distances : List Nat) (recorded : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_running_patterns_bounds (n k : Nat) (distances recorded : List Nat)
    (hn : n ≥ 2) (hk : k > 0) (hk2 : k < n)
    (hdist : distances.length = n)
    (hdist_sorted : ∀ i j, i < j → j < n → distances.get! i ≤ distances.get! j)
    (hdist_unique : ∀ i j, i < j → j < n → distances.get! i ≠ distances.get! j)
    (hrec : recorded.length = k) :
    let result := solve_running_patterns n k distances recorded
    0 ≤ result ∧ result ≤ n - k :=
sorry

theorem solve_running_patterns_self_match (n k : Nat) (distances : List Nat)
    (hn : n ≥ 3) (hk : k > 0) (hk2 : k < n)
    (hdist : distances.length = n)
    (hdist_sorted : ∀ i j, i < j → j < n → distances.get! i ≤ distances.get! j)
    (hdist_unique : ∀ i j, i < j → j < n → distances.get! i ≠ distances.get! j) :
    let diffs := List.zipWith (fun x y => x - y) (distances.drop 1) distances
    let pattern := List.take k diffs
    solve_running_patterns n k distances pattern ≥ 1 :=
sorry

theorem solve_running_patterns_basic_cases :
    solve_running_patterns 2 1 [1,2] [1] = 1 ∧
    solve_running_patterns 3 1 [1,2,3] [1] = 2 :=
sorry
-- </vc-theorems>