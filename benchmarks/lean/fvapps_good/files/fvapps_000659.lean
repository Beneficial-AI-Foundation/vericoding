-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_snackdown_spread (n : Nat) (arr : List Nat) : Nat := sorry

theorem spread_properties_nonnegative (n : Nat) (arr : List Nat) 
  (h1 : arr.length = n) 
  (h2 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 5)
  : solve_snackdown_spread n arr ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem spread_properties_upper_bound (n : Nat) (arr : List Nat)
  (h1 : arr.length = n)
  (h2 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 5) 
  : solve_snackdown_spread n arr ≤ n := sorry

theorem spread_properties_first_valid (n : Nat) (arr : List Nat)
  (h1 : arr.length = n)
  (h2 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 5)
  (h3 : arr ≠ [])
  : ∃ x, arr.head? = some x ∧ x ≥ 1 := sorry

theorem spread_deterministic (n : Nat) (arr : List Nat)
  (h1 : arr.length = n)
  (h2 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 5)
  : solve_snackdown_spread n arr = solve_snackdown_spread n arr := sorry

theorem minimal_valid_array (n : Nat) 
  : solve_snackdown_spread n (List.replicate n 1) ≤ n := sorry
-- </vc-theorems>