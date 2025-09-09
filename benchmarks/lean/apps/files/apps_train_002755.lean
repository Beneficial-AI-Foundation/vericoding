def ka_co_ka_de_ka_me (s: String) : String := sorry

/- Helper functions -/

def isVowel (c: Char) : Bool := sorry
def removeKa (s: String) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

def getConsonants (s: String) : String := sorry

theorem ka_prefix (word: String) :
  String.isPrefixOf "ka" (ka_co_ka_de_ka_me word) := sorry

theorem length_increases (word: String) : 
  word.length > 0 → (ka_co_ka_de_ka_me word).length > word.length := sorry

theorem all_vowels (word: String) :
  (∀ c ∈ word.data, isVowel c) →
  ka_co_ka_de_ka_me word = "ka" ++ word := sorry

theorem consonants_unchanged (word: String) :
  getConsonants word = getConsonants (removeKa (ka_co_ka_de_ka_me word)) := sorry

/-
info: 'kaa'
-/
-- #guard_msgs in
-- #eval ka_co_ka_de_ka_me "a"

/-
info: 'kamaikantekanakance'
-/
-- #guard_msgs in
-- #eval ka_co_ka_de_ka_me "maintenance"

/-
info: 'kaIkancokamprekahekansikabikalikatiekas'
-/
-- #guard_msgs in
-- #eval ka_co_ka_de_ka_me "Incomprehensibilities"

-- Apps difficulty: introductory
-- Assurance level: unguarded