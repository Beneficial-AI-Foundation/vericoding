-- <vc-preamble>
def small_primes : List Nat := [2, 3, 5, 7, 11, 13, 17, 19]
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def aks_test : Nat → Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem known_small_primes_correct (n : Nat) (h : 2 ≤ n ∧ n < 20) :
  aks_test n = true ↔ n ∈ small_primes := by 
sorry

theorem numbers_less_than_2_not_prime {n : Nat} (h : n ≤ 1) :
  aks_test n = false := by 
sorry

theorem prime_divisibility {n : Nat} (h : n ≥ 2) :
  aks_test n = true → ∀ d : Nat, 2 ≤ d → d < n → ¬(n % d = 0) := by 
sorry

theorem composite_has_divisor {n : Nat} (h₁ : n ≥ 2) (h₂ : aks_test n = false) :
  ∃ d : Nat, 2 ≤ d ∧ d < n ∧ n % d = 0 := by 
sorry

theorem product_not_prime {n m : Nat} (h₁ : n > 1) (h₂ : m > 1) (h₃ : n * m ≤ 10000) :
  aks_test (n * m) = false := by 
sorry

theorem aks_consistency (n : Nat) (h : n ≥ 2) :
  aks_test n = aks_test n := by 
sorry
-- </vc-theorems>