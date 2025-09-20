-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_dynamic_string (s : String) : String := sorry

theorem dynamic_string_returns_valid_outputs (s : String) (h : s.length > 0) :
  is_dynamic_string s = "Dynamic" ∨ is_dynamic_string s = "Not" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem few_unique_chars_is_dynamic (s : String) (h1 : s.length > 0) 
    (h2 : (List.map Char.toString s.data).eraseDups.length < 3) : 
  is_dynamic_string s = "Dynamic" := sorry

theorem binary_string_is_dynamic (s : String) (h1 : s.length > 0)
    (h2 : ∀ c ∈ s.data, c = 'a' ∨ c = 'b') :
  is_dynamic_string s = "Dynamic" := sorry

theorem single_char_is_dynamic (c : Char) :
  is_dynamic_string (String.mk [c]) = "Dynamic" := sorry

theorem repeated_char_is_dynamic (c : Char) (n : Nat) (h : n > 0) :
  is_dynamic_string (String.mk (List.replicate n c)) = "Dynamic" := sorry

theorem equal_freq_three_chars_not_dynamic (s : String) (h1 : s.length ≥ 6)
    (h2 : ∀ c ∈ s.data, c = 'a' ∨ c = 'b' ∨ c = 'c')
    (h3 : (s.data.filter (· = 'a')).length = (s.data.filter (· = 'b')).length)
    (h4 : (s.data.filter (· = 'b')).length = (s.data.filter (· = 'c')).length) :
  is_dynamic_string s = "Not" := sorry
-- </vc-theorems>