-- <vc-helpers>
-- </vc-helpers>

def top_3_words (s : String) : List String := sorry 

theorem empty_string_returns_empty_list :
  top_3_words "" = [] := sorry

theorem space_returns_empty_list :
  top_3_words " " = [] := sorry

theorem special_chars_return_empty_list (s : String) :
  (∀ c ∈ s.data, !c.isAlpha ∧ c ≠ '\'') → 
  top_3_words s = [] := sorry

theorem simple_word_count :
  top_3_words "aaa bbb aaa ccc bbb aaa" = ["aaa", "bbb", "ccc"] := sorry

theorem case_insensitive_count :
  top_3_words "AAA bbb AAA ccc BBB aaa" = ["aaa", "bbb", "ccc"] := sorry

theorem valid_apostrophes :
  top_3_words "can't won't don't can't won't can't" = ["can't", "won't", "don't"] := sorry

/-
info: ['a', 'of', 'on']
-/
-- #guard_msgs in
-- #eval top_3_words "In a village of La Mancha, the name of which I have no desire to call to \n            mind, there lived not long since one of those gentlemen that keep a lance\n            in the lance-rack, an old buckler, a lean hack, and a greyhound for\n            coursing. An olla of rather more beef than mutton, a salad on most\n            nights, scraps on Saturdays, lentils on Fridays, and a pigeon or so extra\n            on Sundays, made away with three-quarters of his income."

/-
info: ['e', 'ddd', 'aa']
-/
-- #guard_msgs in
-- #eval top_3_words "e e e e DDD ddd DdD: ddd ddd aa aA Aa, bb cc cC e e e"

/-
info: ["won't", 'wont']
-/
-- #guard_msgs in
-- #eval top_3_words "  //wont won"t won"t"

-- Apps difficulty: interview
-- Assurance level: unguarded