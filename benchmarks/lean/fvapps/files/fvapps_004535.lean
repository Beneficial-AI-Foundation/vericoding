-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count (s : String) (pattern : String) : Nat :=
  sorry

def SENTENCE : String :=
  sorry

def SYLLABLE : String :=
  sorry

def flesch_kincaid (text : String) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem flesch_kincaid_result_is_float (text : String) (h : text.length > 0) :
  ∃ (f : Float), flesch_kincaid text = f :=
sorry

theorem flesch_kincaid_count_properties (text : String)
  (h₁ : text.length > 0)
  (h₂ : count text SENTENCE = 1) :
  let words := count text " " + 1
  let sentences := count text SENTENCE
  let syllables := count text SYLLABLE
  words ≥ 1 ∧
  sentences = 1 ∧
  syllables ≥ 0 ∧
  syllables ≤ text.length :=
sorry

theorem syllable_counting_vowels_only (text : String)
  (h₁ : text.length > 0)
  (h₂ : ∀ c ∈ text.data, c ∈ ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']) :
  let syllables := count text SYLLABLE
  syllables ≥ 1 ∧ syllables ≤ text.length :=
sorry

theorem flesch_kincaid_is_finite (words : List String)
  (h : words.length > 0)
  (h₂ : ∀ w ∈ words, w.length > 0)
  (h₃ : ∀ w ∈ words, ∀ c ∈ w.data, c.isLower) :
  let sentence := String.intercalate " " words ++ "."
  ∃ (result : Float), flesch_kincaid sentence = result :=
sorry
-- </vc-theorems>