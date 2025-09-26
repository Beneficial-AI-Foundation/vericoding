-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def to_roman (n : Nat) : String := sorry
def from_roman (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem roundtrip_roman_numerals (n : Nat) 
  (h : 1 ≤ n ∧ n ≤ 3999) : 
  from_roman (to_roman n) = n := sorry

theorem valid_roman_characters (n : Nat)
  (h : 1 ≤ n ∧ n ≤ 3999) :
  ∀ c, String.contains (to_roman n) c → 
    c = 'I' ∨ c = 'V' ∨ c = 'X' ∨ c = 'L' ∨ c = 'C' ∨ c = 'D' ∨ c = 'M' := sorry

theorem no_invalid_subtractions (n : Nat)
  (h : 1 ≤ n ∧ n ≤ 3999) :
  ¬ String.endsWith (to_roman n) "IL" ∧
  ¬ String.endsWith (to_roman n) "IC" ∧
  ¬ String.endsWith (to_roman n) "ID" ∧
  ¬ String.endsWith (to_roman n) "IM" ∧
  ¬ String.endsWith (to_roman n) "XD" ∧
  ¬ String.endsWith (to_roman n) "XM" ∧
  ¬ String.endsWith (to_roman n) "VX" ∧
  ¬ String.endsWith (to_roman n) "VL" ∧
  ¬ String.endsWith (to_roman n) "VC" ∧
  ¬ String.endsWith (to_roman n) "VD" ∧
  ¬ String.endsWith (to_roman n) "VM" ∧
  ¬ String.endsWith (to_roman n) "LC" ∧
  ¬ String.endsWith (to_roman n) "LD" ∧
  ¬ String.endsWith (to_roman n) "LM" ∧
  ¬ String.endsWith (to_roman n) "DM" := sorry

theorem max_consecutive_chars (n : Nat)
  (h : 1 ≤ n ∧ n ≤ 3999) :
  ¬ String.endsWith (to_roman n) "IIII" ∧
  ¬ String.endsWith (to_roman n) "VVVV" ∧
  ¬ String.endsWith (to_roman n) "XXXX" ∧
  ¬ String.endsWith (to_roman n) "LLLL" ∧
  ¬ String.endsWith (to_roman n) "CCCC" ∧
  ¬ String.endsWith (to_roman n) "DDDD" ∧
  ¬ String.endsWith (to_roman n) "MMMM" := sorry

theorem from_roman_valid_output (s : String)
  (h : ∀ c, String.contains s c → 
    c = 'I' ∨ c = 'V' ∨ c = 'X' ∨ c = 'L' ∨ c = 'C' ∨ c = 'D' ∨ c = 'M') :
  1 ≤ from_roman s ∧ from_roman s ≤ 3999 := sorry
-- </vc-theorems>