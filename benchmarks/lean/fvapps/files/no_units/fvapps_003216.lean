-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Nat.sqrt (n : Nat) : Nat := sorry

def lucas_lehmer (n : Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lucas_lehmer_returns_bool (n : Nat) : 
  lucas_lehmer n = true ∨ lucas_lehmer n = false := sorry

theorem lucas_lehmer_less_than_two (n : Nat) :
  n < 2 → lucas_lehmer n = false := sorry

theorem lucas_lehmer_two :
  lucas_lehmer 2 = true := sorry

theorem lucas_lehmer_even (n : Nat) :
  n > 2 → n % 2 = 0 → lucas_lehmer n = false := sorry

theorem lucas_lehmer_composite (n : Nat) :
  n > 2 → (∃ i : Nat, 2 ≤ i ∧ i * i ≤ n ∧ n % i = 0) → 
  lucas_lehmer n = false := sorry

theorem lucas_lehmer_large (n : Nat) :
  n > 12000 → lucas_lehmer n = false := sorry

theorem lucas_lehmer_non_positive (n : Int) :
  n ≤ 0 → lucas_lehmer n.natAbs = false := sorry
-- </vc-theorems>