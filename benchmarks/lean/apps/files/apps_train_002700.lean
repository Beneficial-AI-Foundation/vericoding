-- <vc-helpers>
-- </vc-helpers>

def char_concat (s : String) : String := sorry

theorem spaces_handling (word : String) :
  char_concat word = char_concat (word.replace " " "") := sorry

theorem first_pair {word : String} (h : word.length ≥ 2) :
  let result := char_concat word
  (result.data[0]! = word.data[0]!) ∧ 
  (result.data[1]! = word.data[word.length - 1]!) ∧
  (result.data[2]! = '1') := sorry

/-
info: 'af1be2cd3'
-/
-- #guard_msgs in
-- #eval char_concat "abcdef"

/-
info: 'Cs1or2da3eW4'
-/
-- #guard_msgs in
-- #eval char_concat "CodeWars"

/-
info: '101292383474565'
-/
-- #guard_msgs in
-- #eval char_concat "1234567890"

-- Apps difficulty: introductory
-- Assurance level: unguarded