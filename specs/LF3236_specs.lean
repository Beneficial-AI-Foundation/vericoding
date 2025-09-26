-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digits (n : Nat) : List Nat := sorry

def is_pandigital (n : Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_pandigital_unique_digits (n : Nat) : 
  is_pandigital n = true →
  ∀ (d₁ d₂ : Nat), d₁ ∈ digits n → d₂ ∈ digits n → (d₁ = d₂) := sorry

theorem is_pandigital_no_zero (n : Nat) :
  is_pandigital n = true →
  0 ∉ digits n := sorry

theorem is_pandigital_valid_range (n : Nat) :
  is_pandigital n = true →
  ∀ d, d ∈ digits n → 1 ≤ d ∧ d ≤ 9 := sorry
-- </vc-theorems>