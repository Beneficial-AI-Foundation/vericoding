-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tops (s : String) : String := sorry

-- Empty string returns empty string
-- </vc-definitions>

-- <vc-theorems>
theorem tops_empty_string :
  tops "" = "" := by sorry

-- Single char string returns empty string

theorem tops_single_char (c : Char) :
  tops (String.mk [c]) = "" := by sorry

-- Output chars are subset of input chars

theorem tops_chars_in_input {s : String} {c : Char} :
  c ∈ (tops s).data → c ∈ s.data := by sorry

-- Simple version of output length follows pattern

theorem tops_output_length {s : String} (h : s.length > 0) :
  ∃ n, (tops s).length = n ∧ n ≥ 0 := by sorry

-- Simple version of output order

theorem tops_output_order {s : String} (h : s.length ≥ 10) :
  ∃ chars : List Char, 
    tops s = String.mk chars ∧
    ∀ c ∈ chars, c ∈ s.data := by sorry

-- Output is deterministic

theorem tops_deterministic {s : String} :
  tops s = tops s := by sorry
-- </vc-theorems>