-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_prime : Nat → Bool := sorry

def step : Nat → Nat → Nat → Option (Nat × Nat) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_prime_properties (n : Nat) :
  (n ≤ 1 → is_prime n = false) ∧ 
  (is_prime n = true → n > 1) := sorry

theorem step_basic_properties (g : Nat) (h : g ≥ 2 ∧ g ≤ 1000) :
  match step g 2 (g + 4) with
  | none => True  
  | some (a, b) => 
      is_prime a = true ∧ 
      is_prime b = true ∧ 
      b - a = g
  := sorry

theorem step_range_properties (g m n : Nat)
  (h₁ : g ≥ 2 ∧ g ≤ 100)
  (h₂ : m ≥ 2 ∧ m ≤ 1000)
  (h₃ : n ≥ 2 ∧ n ≤ 1000) :
  (m ≥ n → step g m n = none) ∧
  (m < n → 
    match step g m n with
    | none => True
    | some (a, b) => 
        m ≤ a ∧ a ≤ b ∧ b ≤ n ∧ 
        b - a = g
    ) := sorry

theorem step_consecutive_ranges (g : Nat) (h : g ≥ 2 ∧ g ≤ 50) :
  ∀ i : Nat,
  i ≥ 10 ∧ i ≤ 90 →
  match step g i (i + 20), step g i (i + 30) with
  | some (a₁, _), some (a₂, _) => a₁ ≤ a₂
  | _, _ => True
  := sorry
-- </vc-theorems>