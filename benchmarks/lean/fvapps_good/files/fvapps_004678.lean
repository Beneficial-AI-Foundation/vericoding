-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution (n : Nat) : String := sorry

def toDigits (n : Nat) : List Char := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_length (n : Nat) (h : n ≤ 99999) :
  (solution n).length = 14 ∧ 
  (solution n).startsWith "Value is " ∧
  ((solution n).drop 9).all Char.isDigit := sorry

theorem solution_padding (n : Nat) (h : n ≤ 99999) :
  let padded := (solution n).takeRight 5
  padded.length = 5 ∧
  padded.toNat? = some n := sorry
-- </vc-theorems>