-- <vc-preamble>
def MOD := 998244353
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_test (n : Nat) (numbers : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_test_within_mod_bounds
  (n : Nat) (numbers : List Nat) (h1 : numbers.length = n) (h2 : n ≥ 1) (h3 : n ≤ 9)
  (h4 : ∀ x ∈ numbers, 1 ≤ x ∧ x ≤ 10^9) :
  0 ≤ solve_test n numbers ∧ solve_test n numbers < MOD :=
sorry

theorem solve_test_order_independent
  (n : Nat) (numbers : List Nat) (h1 : numbers.length = n) (h2 : n ≥ 1) (h3 : n ≤ 9)
  (h4 : ∀ x ∈ numbers, 1 ≤ x ∧ x ≤ 10^9) :
  solve_test n numbers = solve_test n numbers.reverse :=
sorry

theorem solve_test_large_identical_numbers
  (n : Nat) (v : Nat) (h1 : n ≥ 2) (h2 : n ≤ 9) (h3 : v = 10^9)
  (numbers : List Nat) (h4 : numbers = List.replicate n v) :
  0 ≤ solve_test n numbers ∧ solve_test n numbers < MOD :=
sorry
-- </vc-theorems>