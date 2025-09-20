-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hasUniqueDigits (n : Nat) : Bool := sorry

def nextNumb (n : Nat) : Nat ⊕ String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nextNumb_greater (n : Nat) 
  (h : ∃ (m : Nat), nextNumb n = Sum.inl m) :
  (Classical.choose h) > n := sorry

theorem nextNumb_div_three (n : Nat)
  (h : ∃ (m : Nat), nextNumb n = Sum.inl m) :
  (Classical.choose h) % 3 = 0 := sorry

theorem nextNumb_odd (n : Nat)
  (h : ∃ (m : Nat), nextNumb n = Sum.inl m) :
  (Classical.choose h) % 2 = 1 := sorry

theorem nextNumb_unique_digits (n : Nat)
  (h : ∃ (m : Nat), nextNumb n = Sum.inl m) :
  hasUniqueDigits (Classical.choose h) = true := sorry

theorem nextNumb_minimal (n : Nat)
  (h : ∃ (m : Nat), nextNumb n = Sum.inl m) :
  ∀ k : Nat, n < k ∧ k < (Classical.choose h) →
  ¬(k % 3 = 0 ∧ k % 2 = 1 ∧ hasUniqueDigits k = true) := sorry

theorem nextNumb_too_large (n : Nat)
  (h : n ≥ 9876543210) :
  ∃ msg : String, nextNumb n = Sum.inr msg := sorry
-- </vc-theorems>