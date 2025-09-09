-- <vc-helpers>
-- </vc-helpers>

def maxMultiple (divisor: Nat) (bound: Nat) : Nat :=
  sorry

theorem max_multiple_is_divisible (divisor: Nat) (bound: Nat) (h1: divisor > 0)
    : divisor ∣ maxMultiple divisor bound :=
  sorry

theorem max_multiple_within_bound (divisor: Nat) (bound: Nat) (h1: divisor > 0)
    : maxMultiple divisor bound ≤ bound :=
  sorry

theorem max_multiple_is_maximal (divisor: Nat) (bound: Nat) (h1: divisor > 0)
    : maxMultiple divisor bound + divisor > bound :=
  sorry

theorem max_multiple_when_equal (divisor: Nat) (h1: divisor > 0) 
    : maxMultiple divisor divisor = divisor :=
  sorry

theorem max_multiple_zero_invalid (bound: Nat)
    : maxMultiple 0 bound = 0 :=
  sorry

-- Apps difficulty: introductory
-- Assurance level: guarded