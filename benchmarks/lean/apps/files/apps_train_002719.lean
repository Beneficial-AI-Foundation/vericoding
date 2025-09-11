-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def splitSentence (s : String) : List String := sorry

theorem split_sentence_rejoin (s : String) : 
  String.intercalate " " (splitSentence s) = String.intercalate " " (s.split (· = ' ')) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem split_sentence_nonempty_parts (s : String) :
  ∀ part ∈ splitSentence s, part.length > 0 := sorry

theorem split_sentence_no_whitespace (s : String) :
  ∀ part ∈ splitSentence s, ' ' ∉ part.data := sorry

/-
info: ['This', 'string', 'is', 'splitsville']
-/
-- #guard_msgs in
-- #eval splitSentence "This string is splitsville"

/-
info: ['something']
-/
-- #guard_msgs in
-- #eval splitSentence "something"

/-
info: ['hello', 'world']
-/
-- #guard_msgs in
-- #eval splitSentence "hello world"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded