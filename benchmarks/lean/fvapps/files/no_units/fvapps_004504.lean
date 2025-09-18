-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def to_acronym (s: String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem to_acronym_property {words: List String} (h: ∀ w ∈ words, w.length > 0)
  (h₂: words.length > 0) :
  let phrase := String.join (" " :: words.intersperse " ") 
  let acronym := to_acronym phrase
  acronym.length = words.length ∧                    -- Length matches
  (∀ c ∈ acronym.data, c.isUpper) ∧                 -- All chars uppercase
  acronym.data = words.map (λ w => w.front.toUpper) -- First letters match
:= sorry

theorem to_acronym_empty_input (s: String)
  (h: s.trim = "") : 
  to_acronym s = ""
:= sorry
-- </vc-theorems>