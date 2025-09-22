-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mutate_string (s : String) (pos : Nat) (c : Char) : String := sorry

theorem mutate_string_char_at_pos
  {s : String} {pos : Nat} {c : Char} (h1 : s.length > 0) (h2 : pos < s.length) :
  (mutate_string s pos c).get (String.Pos.mk pos) = c := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mutate_string_unchanged_before_pos
  {s : String} {pos : Nat} {c : Char} (h1 : s.length > 0) (h2 : pos < s.length) :
  ∀ i, i < pos → (mutate_string s pos c).get (String.Pos.mk i) = s.get (String.Pos.mk i) := sorry

theorem mutate_string_unchanged_after_pos
  {s : String} {pos : Nat} {c : Char} (h1 : s.length > 0) (h2 : pos < s.length) :
  ∀ i, pos < i → i < s.length → (mutate_string s pos c).get (String.Pos.mk i) = s.get (String.Pos.mk i) := sorry

theorem mutate_single_char
  {c : Char} :
  mutate_string "a" 0 c = String.mk [c] := sorry
-- </vc-theorems>