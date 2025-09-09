-- <vc-helpers>
-- </vc-helpers>

def soundex (name : String) : String := sorry

theorem soundex_length_first_letter_prop {name : String} (h: name.length > 0):
  let codes := (soundex name).split (· = ' ')
  let words := name.split (· = ' ')
  codes.length = words.length ∧ 
  (∀ code ∈ codes, code.length = 4) ∧
  (∀ (w c : String), w ∈ words → c ∈ codes → w.toUpper.front = c.front) := sorry

/-
info: 'S600 C560'
-/
-- #guard_msgs in
-- #eval soundex "Sarah Connor"

/-
info: 'A261'
-/
-- #guard_msgs in
-- #eval soundex "Ashcraft"

/-
info: 'T522'
-/
-- #guard_msgs in
-- #eval soundex "Tymczak"

-- Apps difficulty: introductory
-- Assurance level: unguarded