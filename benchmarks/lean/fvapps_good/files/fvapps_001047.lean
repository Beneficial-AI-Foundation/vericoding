-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isAlternatingCode (s : String) : Bool := sorry

abbrev charAt (s : String) (i : Nat) : Char := 
  s.data[i]'sorry
-- </vc-definitions>

-- <vc-theorems>
theorem alternating_code_first_two_different {s : String} :
  isAlternatingCode s → String.length s ≥ 2 → charAt s 0 ≠ charAt s 1 := sorry 

theorem alternating_code_even_indices {s : String} {i : Nat} :
  isAlternatingCode s → String.length s ≥ 2 → 
  i < String.length s → i % 2 = 0 → charAt s i = charAt s 0 := sorry

theorem alternating_code_odd_indices {s : String} {i : Nat} :
  isAlternatingCode s → String.length s ≥ 2 →
  i < String.length s → i % 2 = 1 → charAt s i = charAt s 1 := sorry

theorem alternating_code_two_chars {s : String} :
  String.length s = 2 → 
  isAlternatingCode s = (charAt s 0 ≠ charAt s 1) := sorry
-- </vc-theorems>