-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def has_unique_chars (s : String) : Bool := sorry

theorem empty_string_has_unique_chars :
  has_unique_chars "" = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem string_with_duplicates_not_unique (s : String) :
  has_unique_chars (s ++ String.mk [s.get! 0]) = false := sorry

theorem len_eq_set_len_iff_unique (s : String) :
  has_unique_chars s = (s.length = s.data.eraseDups.length) := sorry

theorem adding_new_char_preserves_uniqueness (s : String) (c : Char)
  (h1 : has_unique_chars s = true) 
  (h2 : ∀ x ∈ s.data, x ≠ c) :
  has_unique_chars (String.push s c) = true := sorry

theorem concat_unique_strings (s1 s2 : String)
  (h1 : has_unique_chars s1 = true)
  (h2 : has_unique_chars s2 = true)
  (h3 : ∀ x ∈ s1.data, ∀ y ∈ s2.data, x ≠ y) :
  has_unique_chars (s1 ++ s2) = true := sorry
-- </vc-theorems>