-- <vc-preamble>
def isVowel (c : Char) : Bool :=
  c = 'a' || c = 'e' || c = 'i' || c = 'o' || c = 'u'

def WORD_LIST : List String :=
  ["strength", "afterwards", "background", "photograph", "successful", "understand"]
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def wanted_words (vowel_count : Nat) (consonant_count : Nat) (forbidden : List Char) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_are_strings (v c : Nat) (f : List Char) :
  ∀ (w : String), w ∈ wanted_words v c f → w.length ≥ 0
  :=
sorry

theorem exact_vowel_count (v c : Nat) (f : List Char) :
  ∀ (w : String), w ∈ wanted_words v c f →
  (List.filter isVowel w.data).length = v
  :=
sorry

theorem exact_total_length (v c : Nat) (f : List Char) :
  ∀ (w : String), w ∈ wanted_words v c f →
  w.length = v + c
  :=
sorry

theorem no_forbidden_chars (v c : Nat) (f : List Char) :
  ∀ (w : String), w ∈ wanted_words v c f →
  ∀ (x : Char), x ∈ f → ¬(x ∈ w.data)
  :=
sorry
-- </vc-theorems>