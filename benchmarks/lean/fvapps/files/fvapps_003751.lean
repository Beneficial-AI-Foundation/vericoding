-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_word (input : String) : Option (List String) := sorry

theorem longest_word_valid_format 
  (letters : String)
  (h : (longest_word letters).isSome) :
  let result := Option.get! (longest_word letters)
  ∀ w₁ ∈ result, ∀ w₂ ∈ result,
    w₁.length = w₂.length ∧ 
    result.length > 0 :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem longest_word_letter_constraints
  (letters : String)
  (h : (longest_word letters).isSome) :
  let result := Option.get! (longest_word letters)
  ∀ word ∈ result,
  ∀ c, c ∈ word.data →  
  (word.data.count c) ≤ (letters.data.count c) :=
sorry

theorem longest_word_edge_cases :
  longest_word "" = none ∧
  longest_word "123" = none :=
sorry

theorem longest_word_maximal
  (letters : String)
  (h : (longest_word letters).isSome)
  (testWord : String)
  (hValidWord : ∀ c, c ∈ testWord.data → (testWord.data.count c) ≤ (letters.data.count c)) :
  testWord.length ≤ (Option.get! (longest_word letters)).head!.length :=
sorry
-- </vc-theorems>