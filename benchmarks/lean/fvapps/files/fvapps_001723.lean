-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_prime (n : Nat) : Bool :=
  sorry

def statement1 (s : Nat) : Bool :=
  sorry

def statement2 (p : Nat) : Bool :=
  sorry

def statement3 (s : Nat) : Bool :=
  sorry

def is_solution (a b : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem small_numbers_not_prime {n : Nat} (h : n ≤ 1) :
  is_prime n = false :=
sorry

theorem prime_divisibility {n : Nat} (h₁ : n ≥ 2) (h₂ : n ≤ 1000) :
  is_prime n = true → ∀ i : Nat, 2 ≤ i ∧ i ≤ n^(1/2) → n % i ≠ 0 :=
sorry

theorem statement1_even {s : Nat} (h : s % 2 = 0) :
  statement1 s = false :=
sorry

theorem statement1_prime_diff {s : Nat} (h : is_prime (s - 2)) :
  statement1 s = false :=
sorry

theorem statement2_type {p : Nat} (h₁ : p ≥ 4) (h₂ : p ≤ 100) :
  statement2 p = true ∨ statement2 p = false :=
sorry

theorem statement2_composite {p : Nat} (h₁ : p ≥ 4) (h₂ : p ≤ 100) :
  statement2 p = true → ∃ i : Nat, 2 ≤ i ∧ i ≤ p^(1/2) ∧ p % i = 0 :=
sorry

theorem statement3_type {s : Nat} (h₁ : s ≥ 4) (h₂ : s ≤ 100) :
  statement3 s = true ∨ statement3 s = false :=
sorry

theorem statement3_small {s : Nat} (h : s ≤ 3) :
  statement3 s = false :=
sorry

theorem is_solution_type {a b : Nat} (h₁ : a ≥ 2) (h₂ : a ≤ 50) (h₃ : b ≥ 2) (h₄ : b ≤ 50) :
  is_solution a b = true ∨ is_solution a b = false :=
sorry

theorem is_solution_constraints {a b : Nat} (h₁ : (a + b) % 2 = 0 ∨ is_prime (a * b)) :
  is_solution a b = false :=
sorry
-- </vc-theorems>