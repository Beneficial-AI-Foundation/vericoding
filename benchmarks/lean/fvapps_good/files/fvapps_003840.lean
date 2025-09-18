-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toLeetSpeak (s : String) : String := sorry

theorem toLeetSpeak_preserves_length_uppercase (s : String)
  (h : ∀ c ∈ s.data, c.isUpper) :
  (toLeetSpeak s).length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem toLeetSpeak_result_is_string (s : String)
  (h : ∀ c ∈ s.data, c.isUpper) :
  ∃ _r : String, toLeetSpeak s = _r := sorry

theorem toLeetSpeak_valid_chars (s : String)
  (h : ∀ c ∈ s.data, c.isUpper ∨ c = ' ') :
  ∀ c ∈ (toLeetSpeak s).data,
    (c.isUpper ∨ 
     c ∈ ['!', '@', '#', '$', '%', '^', '&', '*', '(', ')', 
          '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', ' ']) := sorry

theorem toLeetSpeak_empty :
  toLeetSpeak "" = "" := sorry

theorem toLeetSpeak_known_mappings :
  toLeetSpeak "A" = "@" ∧
  toLeetSpeak "E" = "3" ∧
  toLeetSpeak "I" = "!" ∧
  toLeetSpeak "O" = "0" ∧
  toLeetSpeak "S" = "$" ∧
  toLeetSpeak "T" = "7" := sorry
-- </vc-theorems>