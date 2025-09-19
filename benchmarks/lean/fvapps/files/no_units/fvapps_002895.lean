-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def thue_morse (n : Nat) : String := sorry

/- The length of thue_morse(n) equals n and contains only 0's and 1's -/
-- </vc-definitions>

-- <vc-theorems>
theorem thue_morse_length (n : Nat) : 
  (thue_morse n).length = n ∧ 
  ∀ p : String.Pos, 
    String.contains "01" ((thue_morse n).get p) := sorry
-- </vc-theorems>