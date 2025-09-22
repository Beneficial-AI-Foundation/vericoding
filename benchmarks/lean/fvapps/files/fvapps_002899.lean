-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>