-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_read_words (known_letters : String) (word_list : List String) : List String := sorry

theorem can_read_words_length
  (known_letters : String)
  (word_list : List String)
  (h₁ : known_letters.length > 0) :
  (can_read_words known_letters word_list).length = word_list.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem can_read_words_valid_outputs
  (known_letters : String) 
  (word_list : List String)
  (h₁ : known_letters.length > 0) :
  ∀ x ∈ can_read_words known_letters word_list, x = "Yes" ∨ x = "No" := sorry

theorem can_read_words_yes_implies_all_letters_known
  (known_letters : String)
  (word_list : List String)
  (h₁ : known_letters.length > 0) 
  (i : Nat)
  (h₂ : i < word_list.length)
  (h₃ : (can_read_words known_letters word_list)[i]? = some "Yes") :
  ∀ c ∈ (word_list[i]?.getD "").data, c ∈ known_letters.data := sorry

theorem can_read_words_no_implies_some_letter_unknown
  (known_letters : String)
  (word_list : List String)
  (h₁ : known_letters.length > 0)
  (i : Nat)
  (h₂ : i < word_list.length)
  (h₃ : (can_read_words known_letters word_list)[i]? = some "No") :
  ∃ c ∈ (word_list[i]?.getD "").data, c ∉ known_letters.data := sorry

theorem can_read_words_empty_list
  (known_letters : String)
  (h₁ : known_letters.length > 0) :
  can_read_words known_letters [] = [] := sorry

theorem can_read_words_single_word
  (known_letters : String)
  (word : String)
  (h₁ : known_letters.length > 0) :
  (∀ c ∈ word.data, c ∈ known_letters.data) →
  can_read_words known_letters [word] = ["Yes"] := sorry

theorem can_read_words_single_word_not
  (known_letters : String)
  (word : String)
  (h₁ : known_letters.length > 0) :
  (∃ c ∈ word.data, c ∉ known_letters.data) →
  can_read_words known_letters [word] = ["No"] := sorry
-- </vc-theorems>