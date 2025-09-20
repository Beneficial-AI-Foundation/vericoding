-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isOdd (n : Nat) : Bool :=
  sorry

def split_odd_and_even (n : Nat) : List Nat :=
  sorry

def charToNat (c : Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem split_returns_list (n : Nat) (h : n > 0) :
  ∃ (l : List Nat), split_odd_and_even n = l
  := by
sorry

theorem digits_have_same_parity (n : Nat) (h : n > 0) :
  ∀ x, x ∈ split_odd_and_even n →
    let digits := (toString x).data
    ∀ d, d ∈ digits →
      ∀ h : 0 < digits.length,
        isOdd (charToNat d) = isOdd (charToNat (digits[0]'h))
  := by
sorry
-- </vc-theorems>