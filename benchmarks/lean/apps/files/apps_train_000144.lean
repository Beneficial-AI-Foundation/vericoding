-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decode_string (s: String) : String := sorry

def String.containsChar (s: String) (c: Char) : Prop := 
  s.data.contains c
-- </vc-definitions>

-- <vc-theorems>
theorem decode_string_only_letters (s: String) :
  ∀ c, String.containsChar (decode_string s) c → c.isAlpha := sorry

theorem decode_string_letters_from_input (s: String) :
  ∀ c, String.containsChar (decode_string s) c →
    ∃ c', String.containsChar s c' ∧ c = c' ∧ c'.isAlpha := sorry

theorem decode_string_identity_single (c: Char) (h: c.isAlpha) :
  decode_string (String.singleton c) = String.singleton c := sorry

theorem decode_string_identity_plain (s: String) (h: ∀ c, String.containsChar s c → c.isAlpha) :
  decode_string s = s := sorry

theorem decode_string_simple_repeat (c: Char) (h: c.isAlpha) :
  decode_string s!"2[{String.singleton c}]" = String.singleton c ++ String.singleton c := sorry

/-
info: 'aaabcbc'
-/
-- #guard_msgs in
-- #eval decode_string "3[a]2[bc]"

/-
info: 'accaccacc'
-/
-- #guard_msgs in
-- #eval decode_string "3[a2[c]]"

/-
info: 'abcabccdcdcdef'
-/
-- #guard_msgs in
-- #eval decode_string "2[abc]3[cd]ef"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded