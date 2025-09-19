-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def soundex (name : String) : String := sorry

theorem soundex_length_first_letter_prop {name : String} (h: name.length > 0):
  let codes := (soundex name).split (· = ' ')
  let words := name.split (· = ' ')
  codes.length = words.length ∧ 
  (∀ code ∈ codes, code.length = 4) ∧
  (∀ (w c : String), w ∈ words → c ∈ codes → w.toUpper.front = c.front) := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>