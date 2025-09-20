-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_forgotten_words (dictionary : List String) (phrases : List (List String)) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_repeated_word {word : String} {count : Nat} (h : count > 0) :
  let dictionary := [word]
  let phrases := List.replicate count ["1", word] 
  check_forgotten_words dictionary phrases = "YES" :=
  sorry
-- </vc-theorems>