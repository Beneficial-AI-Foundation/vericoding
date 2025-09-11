-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_string (s : String) : List Char := sorry

variable (words : List String)
variable (spaces : String)
-- </vc-definitions>

-- <vc-theorems>
theorem make_string_words_property (h : ∀ w ∈ words, w.length > 0) :
  let sentence := String.join (List.intersperse " " words)
  let result := make_string sentence
  result.length = words.length ∧
  ∀ i, i < words.length → 
    result.get ⟨i, sorry⟩ = (words.get ⟨i, sorry⟩).data.head! := sorry

theorem make_string_only_spaces (h : ∀ c ∈ spaces.data, c = ' ') :
  make_string spaces = [] := sorry

/-
info: 'sexy'
-/
-- #guard_msgs in
-- #eval make_string "sees eyes xray yoat"

/-
info: 'bean'
-/
-- #guard_msgs in
-- #eval make_string "brown eyes are nice"

/-
info: 'cavn'
-/
-- #guard_msgs in
-- #eval make_string "cars are very nice"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded