-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def charToAscii (s : String) : Option Dict := sorry

theorem charToAscii_empty_string :
  charToAscii "" = none := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem charToAscii_maps_to_ascii (s : String) (c : Char) (d : Dict) :
  s ≠ "" →
  c.isAlpha = true →
  c ∈ s.data →
  charToAscii s = some d →
  ∃ n, (c, n) ∈ d.chars ∧ n = c.toNat := sorry

theorem charToAscii_keys_are_alpha (s : String) (d : Dict) :
  s ≠ "" →
  charToAscii s = some d →
  ∀ c n, (c, n) ∈ d.chars → c.isAlpha = true := sorry

theorem charToAscii_includes_all_alpha (s : String) (d : Dict) : 
  s ≠ "" →
  charToAscii s = some d →
  ∀ c, c ∈ s.data → c.isAlpha = true → 
  ∃ n, (c, n) ∈ d.chars := sorry

theorem charToAscii_non_alpha_empty (s : String) (d : Dict) :
  s ≠ "" →
  (∀ c, c ∈ s.data → c.isAlpha = false) →
  charToAscii s = some d →
  d.chars = [] := sorry

theorem charToAscii_alpha_only_size (s : String) (d : Dict) :
  s ≠ "" →
  (∀ c, c ∈ s.data → c.isAlpha = true) →
  charToAscii s = some d →
  d.chars.length = s.data.eraseDups.length := sorry

/-
info: None
-/
-- #guard_msgs in
-- #eval char_to_ascii ""

/-
info: {'a': 97}
-/
-- #guard_msgs in
-- #eval char_to_ascii "a"

/-
info: {'h': 104, 'e': 101, 'l': 108, 'o': 111, 'w': 119, 'r': 114, 'd': 100}
-/
-- #guard_msgs in
-- #eval char_to_ascii "hello world"
-- </vc-theorems>