-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shortestCompletingWord (licensePlate : String) (words : List String) : Option String :=
sorry

def isAlpha (c : Char) : Bool :=
sorry

def containsAllLetters (word : String) (plate : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shortest_completing_word_in_wordlist (plate : String) (words : List String) :
  ∀ result, shortestCompletingWord plate words = some result →
  ∃ w ∈ words, w.toLower = result.toLower :=
sorry

theorem completes_license_plate (plate : String) (words : List String) :
  ∀ result, shortestCompletingWord plate words = some result →
  ∀ c ∈ plate.toList, isAlpha c → c.toLower ∈ result.toLower.toList :=
sorry

theorem is_shortest_valid_word (plate : String) (words : List String) :
  ∀ result, shortestCompletingWord plate words = some result →
  ∀ w ∈ words, containsAllLetters w plate → result.length ≤ w.length :=
sorry

theorem case_insensitive (plate : String) (words : List String) :
  shortestCompletingWord plate.toLower words = shortestCompletingWord plate.toUpper words :=
sorry

theorem ignore_non_alpha (words : List String) :
  shortestCompletingWord "A1B2C3" words = shortestCompletingWord "ABC" words :=
sorry
-- </vc-theorems>