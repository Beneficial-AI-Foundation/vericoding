-- <vc-preamble>
def is_dd (n : Nat) : Bool := sorry 

def countDigit (n : Nat) (d : Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digits (n : Nat) : List Nat := sorry 

theorem dd_characterization (n : Nat) :
  is_dd n = (∃ d : Nat, 1 ≤ d ∧ d ≤ 9 ∧ countDigit n d = d) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_not_counted (n : Nat) :
  (∀ d : Nat, d ≠ 0 → countDigit n d ≠ d) → 
  is_dd n = false := sorry

theorem count_digit_bounds (n d : Nat) :
  countDigit n d ≤ (digits n).length := sorry
-- </vc-theorems>