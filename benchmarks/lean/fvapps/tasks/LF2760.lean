-- <vc-preamble>
def countSpaces (s : String) : Nat :=
  s.toList.foldl (fun count c => if c = ' ' then count + 1 else count) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def string_transformer (s : String) : String := sorry

def swapcase (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem whitespace_preservation (s : String) :
  countSpaces s = countSpaces (string_transformer s) :=
sorry

theorem word_order_reversal (words : List String) (h : words ≠ []) :
  let s := String.intercalate " " words
  let result := string_transformer s
  let original_words := s.split (· = ' ')
  let result_words := result.split (· = ' ')
  original_words.length = result_words.length ∧
  ∀ (i : Nat), i < original_words.length →
    swapcase (original_words[i]!) = result_words[result_words.length - 1 - i]! :=
sorry
-- </vc-theorems>