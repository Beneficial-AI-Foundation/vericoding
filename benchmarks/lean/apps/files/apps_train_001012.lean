-- <vc-helpers>
-- </vc-helpers>

def check_forgotten_words (dictionary : List String) (phrases : List (List String)) : String :=
  sorry

theorem check_repeated_word {word : String} {count : Nat} (h : count > 0) :
  let dictionary := [word]
  let phrases := List.replicate count ["1", word] 
  check_forgotten_words dictionary phrases = "YES" :=
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible