-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def camelize (s : String) : String := sorry

theorem camelize_not_empty (s : String) (h : s.any fun c => c.isAlpha) :
  (camelize s).length > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem camelize_first_upper (s : String) (h : s.any fun c => c.isAlpha) 
  (h2 : (camelize s).length > 0) :
  Char.isUpper ((camelize s).data.get! 0) := sorry

theorem camelize_no_spaces (s : String) :
  ¬(camelize s).any (· = ' ') := sorry

theorem camelize_no_hyphens (s : String) :
  ¬(camelize s).any (· = '-') := sorry

theorem camelize_no_underscores (s : String) :
  ¬(camelize s).any (· = '_') := sorry

theorem camelize_preserves_word_starts (s : String) (word_start_indices : List Nat)
  (h : ∀ i ∈ word_start_indices, i < s.length) :
  ∀ i ∈ word_start_indices,
    ∃ j < (camelize s).length,
      Char.toLower ((camelize s).data.get! j) = 
      Char.toLower (s.data.get! i) := sorry
-- </vc-theorems>