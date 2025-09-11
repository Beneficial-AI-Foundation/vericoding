-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def to_nato (s : String) : String := sorry

def nato_words : List String := [
  "ALFA", "BRAVO", "CHARLIE", "DELTA", "ECHO", "FOXTROT", "GOLF",
  "HOTEL", "INDIA", "JULIETT", "KILO", "LIMA", "MIKE", "NOVEMBER", 
  "OSCAR", "PAPA", "QUEBEC", "ROMEO", "SIERRA", "TANGO", "UNIFORM",
  "VICTOR", "WHISKEY", "XRAY", "YANKEE", "ZULU"
]
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_string (s : String) : 
  toString (to_nato s) = to_nato s := sorry

theorem preserves_non_alpha_chars (s : String) (c : Char) :
  c ∈ s.data → (¬Char.isAlpha c) → c ≠ ' ' → 
  c.toUpper ∈ (to_nato s).data := sorry

theorem all_alpha_chars_converted (s : String) (word : String) :
  word ∈ (to_nato s).split (· = ' ') →
  (∀ c ∈ word.data, Char.isAlpha c) → 
  word.toUpper ∈ nato_words := sorry

theorem case_insensitive (s : String) :
  to_nato s.toLower = to_nato s.toUpper := sorry

/-
info: 'India Foxtrot Yankee Oscar Uniform Charlie Alfa November Romeo Echo Alfa Delta'
-/
-- #guard_msgs in
-- #eval to_nato "If you can read"

/-
info: 'Delta India Delta November Oscar Tango Sierra Echo Echo Tango Hotel Alfa Tango Charlie Oscar Mike India November Golf'
-/
-- #guard_msgs in
-- #eval to_nato "Did not see that coming"

/-
info: 'India Foxtrot , Yankee Oscar Uniform Charlie Alfa November Romeo Echo Alfa Delta ?'
-/
-- #guard_msgs in
-- #eval to_nato "If, you can read?"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded