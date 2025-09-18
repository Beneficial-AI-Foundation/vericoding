-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ka_co_ka_de_ka_me (s: String) : String :=
sorry

def isVowel (c: Char) : Bool :=
sorry

def removeKa (s: String) : String :=
sorry

def getConsonants (s: String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ka_prefix (word: String) :
  String.isPrefixOf "ka" (ka_co_ka_de_ka_me word) :=
sorry

theorem length_increases (word: String) :
  word.length > 0 → (ka_co_ka_de_ka_me word).length > word.length :=
sorry

theorem all_vowels (word: String) :
  (∀ c ∈ word.data, isVowel c) →
  ka_co_ka_de_ka_me word = "ka" ++ word :=
sorry

theorem consonants_unchanged (word: String) :
  getConsonants word = getConsonants (removeKa (ka_co_ka_de_ka_me word)) :=
sorry
-- </vc-theorems>