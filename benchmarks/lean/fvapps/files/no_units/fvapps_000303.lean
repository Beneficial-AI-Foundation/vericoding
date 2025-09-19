-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def candy (ratings : List Nat) : Nat := sorry

theorem candy_empty :
  candy [] = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem candy_single (rating : Nat) :
  candy [rating] = 1 := sorry
-- </vc-theorems>