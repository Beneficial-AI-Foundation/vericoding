-- <vc-preamble>
def SWAP : Char → Char
  | 'a' => '@'
  | 'i' => '1'
  | 'e' => '3'
  | 'o' => '0'
  | c => c
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_password (phrase : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem password_length_matches_words (words : List String) :
  (make_password (String.intercalate " " words)).length = words.length :=
  sorry

theorem first_letters_property (words : List String) (h : ∀ w ∈ words, w.length > 0) :
  let pass := make_password (String.intercalate " " words)
  ∀ i < pass.length, ∀ j < words.length, i = j →
    pass.data[i]! = SWAP (words[j]!.data[0]!) :=
  sorry

theorem empty_words_filtered (phrase : String) :
  let clean := String.intercalate " " (phrase.split (· = ' ') |>.filter (·.length > 0))
  make_password phrase = make_password clean :=
  sorry

theorem swap_chars_applied (words : List String) (h : ∀ w ∈ words, w.length > 0) :
  let pass := make_password (String.intercalate " " words)
  ∀ i < pass.length, ∀ j < words.length, i = j →
    let firstChar := words[j]!.data[0]!
    firstChar ∈ ['a', 'i', 'e', 'o'] →
    pass.data[i]! = SWAP firstChar :=
  sorry

/-
info: 'Gml0gmd'
-/
-- #guard_msgs in
-- #eval make_password "Give me liberty or give me death"

/-
info: 'KCaC0'
-/
-- #guard_msgs in
-- #eval make_password "Keep Calm and Carry On"

/-
info: '505'
-/
-- #guard_msgs in
-- #eval make_password "Save Our Souls"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded