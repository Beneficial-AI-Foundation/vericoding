/-
## Task

Complete function `splitOddAndEven`, accept a number `n`(n>0), return an array that contains the continuous parts of odd or even digits.

Please don't worry about digit `0`, it won't appear ;-)

## Examples
-/

def isOdd (n : Nat) : Bool :=
  sorry

def split_odd_and_even (n : Nat) : List Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def charToNat (c : Char) : Nat :=
  sorry

theorem split_returns_list (n : Nat) (h : n > 0) :
  ∃ (l : List Nat), split_odd_and_even n = l
  := by sorry

theorem digits_have_same_parity (n : Nat) (h : n > 0) :
  ∀ x, x ∈ split_odd_and_even n →
    let digits := (toString x).data
    ∀ d, d ∈ digits →
      ∀ h : 0 < digits.length,
        isOdd (charToNat d) = isOdd (charToNat (digits[0]'h))
  := by sorry

-- Apps difficulty: introductory
-- Assurance level: guarded