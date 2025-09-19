-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def timed_reading (maxLength: Int) (text: String) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem timed_reading_non_negative (maxLength: Int) (text: String) :
  timed_reading maxLength text ≥ 0 :=
sorry

theorem timed_reading_is_bounded_by_word_count (maxLength: Int) (text: String) :
  timed_reading maxLength text ≤ (text.split (· = ' ')).length :=
sorry

theorem timed_reading_counts_valid_words (maxLength: Int) (words: List String) :
  let text := String.intercalate " " words
  timed_reading maxLength text = (words.filter (fun w => w.length ≤ maxLength)).length :=
sorry

theorem timed_reading_empty_string :
  timed_reading 0 "" = 0 :=
sorry

theorem timed_reading_no_letters (text: String) :
  (∀ c ∈ text.data, ¬c.isAlpha) →
  timed_reading 1 text = 0 :=
sorry

theorem timed_reading_negative_length :
  timed_reading (-1) "hello" = 0 :=
sorry
-- </vc-theorems>