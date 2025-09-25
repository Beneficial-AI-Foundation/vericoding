-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n : Nat) : Nat :=
sorry

def isPrime (n : Nat) : Bool :=
sorry

def gap (g m n : Nat) : Option (Nat × Nat) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem prime_divisibility {n : Nat} (h : n ≥ 2) :
  isPrime n = true →
  ∀ i : Nat, 2 ≤ i → i ≤ sqrt n → n % i ≠ 0 :=
sorry

theorem composite_divisibility {n : Nat} (h : n ≥ 2) :
  isPrime n = false →
  (∃ i : Nat, 2 ≤ i ∧ i ≤ sqrt n ∧ n % i = 0) ∨ n < 2 :=
sorry

theorem gap_result_valid {g m n : Nat} (hm : m ≥ 2) (hn : n ≥ 2) :
  ∀ result : Nat × Nat,
  gap g m n = some result →
  let (p₁, p₂) := result
  (isPrime p₁ = true ∧ isPrime p₂ = true) ∧
  p₂ - p₁ = g ∧
  m ≤ p₁ ∧ p₁ ≤ p₂ ∧ p₂ ≤ n ∧
  ∀ x : Nat, p₁ < x → x < p₂ → isPrime x = false :=
sorry
-- </vc-theorems>