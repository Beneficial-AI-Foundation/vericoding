-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Nat) (arr : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_output_is_valid
  (n k : Nat)
  (arr : List Nat)
  (h1 : n > 0)
  (h2 : k > 0)
  (h3 : n ≤ 10)
  (h4 : k ≤ 10)
  (h5 : arr.length = n)
  (h6 : ∀ x ∈ arr, x ≤ 10) :
  solve n k arr = 1 ∨ solve n k arr = 2 :=
sorry

theorem solve_is_deterministic
  (n k : Nat)
  (arr : List Nat)
  (h1 : n > 0)
  (h2 : k > 0)
  (h3 : n ≤ 10)
  (h4 : k ≤ 10)
  (h5 : arr.length = n)
  (h6 : ∀ x ∈ arr, x ≥ 0) :
  solve n k arr = solve n k arr :=
sorry

theorem solve_impossible_to_win_with_k_too_large
  (n : Nat)
  (arr : List Nat)
  (h1 : n > 0)
  (h2 : n ≤ 10)
  (h3 : arr.length = n)
  (h4 : ∀ x ∈ arr, x ≥ 0) :
  let k := (arr.foldl (· + ·) 0) + 1
  solve n k arr = 2 :=
sorry

theorem solve_always_wins_with_k_zero
  (n : Nat)
  (arr : List Nat)
  (h1 : n > 0)
  (h2 : n ≤ 10)
  (h3 : arr.length = n)
  (h4 : ∀ x ∈ arr, x ≥ 0)
  (h5 : ∃ x ∈ arr, x > 0) :
  solve n 0 arr = 1 :=
sorry
-- </vc-theorems>