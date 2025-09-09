-- <vc-helpers>
-- </vc-helpers>

def trigrams (s : String) : String := sorry 

def stringToGrams (s : String) : List String := sorry

theorem trigrams_empty_if_short (s : String) :
  s.length < 3 → trigrams s = "" := sorry 

theorem trigrams_length (s : String) :
  s.length ≥ 3 → 
  let res := trigrams s
  res ≠ "" →
  (stringToGrams res).length = s.length - 2 := sorry

theorem trigrams_no_spaces_in_grams (s : String) :
  let res := trigrams s
  let grams := stringToGrams res
  ∀ g ∈ grams, ¬ g.contains ' ' := sorry

/-
info: 'the he_ e_q _qu qui uic ick ck_ k_r _re red'
-/
-- #guard_msgs in
-- #eval trigrams "the quick red"

/-
info: ''
-/
-- #guard_msgs in
-- #eval trigrams "Hi"

/-
info: 'abc bc_ c_d _de def'
-/
-- #guard_msgs in
-- #eval trigrams "abc def"

-- Apps difficulty: introductory
-- Assurance level: unguarded