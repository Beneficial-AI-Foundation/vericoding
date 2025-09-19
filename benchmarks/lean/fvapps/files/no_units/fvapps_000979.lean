-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_running_patterns (n : Nat) (k : Nat) (distances : List Nat) (recorded : List Nat) : Nat :=
  sorry

/- The output is a natural number between 0 and n-k -/
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
-- </vc-theorems>