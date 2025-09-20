-- <vc-preamble>
def isSorted (as : List Nat) : Prop :=
  ∀ i j, i < j → j < as.length → as[i]! ≤ as[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def order (sentence : String) : String :=
  sorry

def splitString (s : String) (sep : Char) : List String :=
  sorry

def findNumber (s : String) : Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem order_preserves_empty_string :
  order "" = "" :=
sorry

theorem order_sorts_by_numbers {sentence : String} {words : List String} :
  words = splitString sentence ' ' →
  let resultWords := splitString (order sentence) ' '
  let numbers := resultWords.filterMap findNumber
  isSorted numbers :=
sorry

theorem order_preserves_words {sentence : String} {words : List String} :
  words = splitString sentence ' ' →
  let resultWords := splitString (order sentence) ' '
  words.eraseDups = resultWords.eraseDups ∧
  words.length = resultWords.length :=
sorry

theorem order_all_properties {sentence : String} {words : List String} :
  words = splitString sentence ' ' →
  (sentence = "" → order sentence = "") ∧
  let resultWords := splitString (order sentence) ' '
  let numbers := resultWords.filterMap findNumber
  isSorted numbers ∧
  words.eraseDups = resultWords.eraseDups ∧
  words.length = resultWords.length :=
sorry
-- </vc-theorems>