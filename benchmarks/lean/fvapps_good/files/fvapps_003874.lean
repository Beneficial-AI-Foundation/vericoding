-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mix_words (s : String) : Option String := sorry

def is_properly_scrambled (original scrambled : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_length_matches_input (s : String) :
  ∀ res, mix_words s = some res → res.length = s.length := sorry

theorem non_letter_strings_unchanged (s : String) :
  (∀ c ∈ s.data, !c.isAlpha) → mix_words s = some s := sorry

theorem word_boundaries_preserved (s : String) (res : String) :
  s.length ≥ 4 → 
  mix_words s = some res →
  res.front = s.front ∧ 
  res.back = s.back := sorry

theorem preserve_chars (s : String) (res : String) :
  mix_words s = some res →
  s.data.toArray = res.data.toArray := sorry

theorem words_properly_scrambled (words : List String) (text : String) (res : String) :
  words ≠ [] →
  (∀ w ∈ words, w ≠ "") →
  text = String.intercalate " " words →
  mix_words text = some res →
  let result_words := res.split (· = ' ')
  words.length = result_words.length := sorry
-- </vc-theorems>