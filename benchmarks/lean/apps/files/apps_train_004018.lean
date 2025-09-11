-- <vc-preamble>
def evenLength (s : String) : Bool :=
  s.length % 2 = 0
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def filterEvenLengthWords (words : List String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_elements_have_even_length (words : List String) :
  ∀ w ∈ filterEvenLengthWords words, evenLength w :=
sorry

theorem output_is_subset_of_input (words : List String) :
  ∀ w ∈ filterEvenLengthWords words, w ∈ words :=
sorry

theorem all_even_length_words_included (words : List String) :
  ∀ w ∈ words, evenLength w → w ∈ filterEvenLengthWords words :=
sorry

theorem maintains_order (words : List String) :
  filterEvenLengthWords words = words.filter evenLength :=
sorry

/-
info: ['word', 'word']
-/
-- #guard_msgs in
-- #eval filter_even_length_words ["word", "words", "word", "words"]

/-
info: []
-/
-- #guard_msgs in
-- #eval filter_even_length_words ["Hello", "World"]

/-
info: ['Four']
-/
-- #guard_msgs in
-- #eval filter_even_length_words ["One", "Two", "Three", "Four"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded