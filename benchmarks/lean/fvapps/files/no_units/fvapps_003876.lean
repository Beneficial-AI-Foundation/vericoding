-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_char (n : Int) : Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_char_ascii {i : Int} (h : 0 ≤ i ∧ i ≤ 127) : 
  Char.toNat (get_char i) = i := 
  sorry

theorem get_char_invalid_neg {i : Int} (h : i < 0) :
  ¬(∃ c : Char, get_char i = c) :=
  sorry

theorem get_char_invalid_large {i : Int} (h : i > 1114111) : 
  ¬(∃ c : Char, get_char i = c) := 
  sorry
-- </vc-theorems>