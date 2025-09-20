-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def kontti (s : String) : String := sorry

theorem kontti_preserves_word_count (s : String) 
  (h : ∃ w : List String, w.all (λ x => ∃ v, v ∈ ['a', 'e', 'i', 'o', 'u'] ∧ v ∈ x.data) ∧ s = String.intercalate " " w) :
  (String.split (kontti s) (· = ' ')).length = (String.split s (· = ' ')).length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem kontti_basic_format (s : String)
  (h : ∃ w : List String, w.all (λ x => ∃ v, v ∈ ['a', 'e', 'i', 'o', 'u'] ∧ v ∈ x.data) ∧ s = String.intercalate " " w) :
  let result := kontti s
  ∀ word ∈ String.split result (· = ' '),
    (∃ i, i + 1 < word.length ∧ 
      word.data[i]? = some 'k' ∧ word.data[i+1]? = some 'o') ∧
    (∃ i : Nat, i + 4 ≤ word.length ∧ word.data.drop i = "ntti".data) ∧
    (word.data.filter (· = '-')).length = 1 := sorry

theorem kontti_vowel_words (s : String)
  (h : ∃ w : List String, w.all (λ x => ∀ c ∈ x.data, c ∈ ['a', 'e', 'i', 'o', 'u']) ∧ s = String.intercalate " " w)
  (h₂ : s ≠ "") :
  let result := kontti s
  ∀ word ∈ String.split result (· = ' '),
    (∃ i, i < word.data.length ∧ word.data[i]? = some '-') ∧
    (∃ i : Nat, i + 4 ≤ word.length ∧ word.data.drop i = "ntti".data) := sorry
-- </vc-theorems>