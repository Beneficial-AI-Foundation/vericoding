-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isLastDigitPretty (n : Nat) : Bool := sorry

def count_pretty_numbers (l r : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_pretty_numbers_non_negative (l r : Nat) : 
  count_pretty_numbers l r ≥ 0 := sorry

theorem count_pretty_numbers_bounded (l r : Nat) :
  count_pretty_numbers l r ≤ (max l r - min l r + 1) := sorry
-- </vc-theorems>