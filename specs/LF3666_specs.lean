-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fire_and_fury (tweet : String) : String := sorry

def containsSubstring (s : String) (sub : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string_fake_tweet :
  fire_and_fury "" = "Fake tweet." := sorry

theorem numeric_input_fake_tweet (n : Nat) :
  fire_and_fury (toString n) = "Fake tweet." := sorry

theorem invalid_chars_fake_tweet {s : String} :
  (∀ c ∈ s.data, c ∉ ['F', 'I', 'R', 'U', 'Y']) →
  fire_and_fury s = "Fake tweet." := sorry

theorem valid_tweet_result {s : String} :
  fire_and_fury s = "Fake tweet." ∨ 
  (fire_and_fury s).endsWith "furious." ∨
  (fire_and_fury s).endsWith "fired!" := sorry

theorem fury_only_result {s : String} :
  (∀ c ∈ s.data, c ∈ ['F', 'U', 'R', 'Y']) →
  (containsSubstring s "FURY" → containsSubstring (fire_and_fury s) "furious" ∧ 
    ¬containsSubstring (fire_and_fury s) "fired") ∧
  (¬containsSubstring s "FURY" → fire_and_fury s = "Fake tweet.") := sorry

theorem no_fire_fury_fake_tweet {s : String} :
  (¬containsSubstring s "FIRE" ∧ ¬containsSubstring s "FURY") →
  fire_and_fury s = "Fake tweet." := sorry

theorem fire_fury_valid_result {s : String} :
  (containsSubstring s "FIRE" ∨ containsSubstring s "FURY") →
  ¬(fire_and_fury s = "Fake tweet.") ∧
  ((fire_and_fury s).endsWith "furious." ∨ (fire_and_fury s).endsWith "fired!") := sorry
-- </vc-theorems>