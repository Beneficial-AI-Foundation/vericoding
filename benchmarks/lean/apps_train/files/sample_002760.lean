/-
Given a string, return a new string that has transformed based on the input:

* Change case of every character, ie. lower case to upper case, upper case to lower case.
* Reverse the order of words from the input.

**Note:** You will have to handle multiple spaces, and leading/trailing spaces.

For example:

```
"Example Input" ==> "iNPUT eXAMPLE"
```

You may assume the input only contain English alphabet and spaces.
-/

def string_transformer (s : String) : String := sorry

def countSpaces (s : String) : Nat :=
  s.toList.foldl (fun count c => if c = ' ' then count + 1 else count) 0

-- <vc-helpers>
-- </vc-helpers>

def swapcase (s : String) : String := sorry

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

/-
info: expected
-/
-- #guard_msgs in
-- #eval string_transformer "Example string"

/-
info: expected
-/
-- #guard_msgs in
-- #eval string_transformer "To be OR not to be That is the Question"

/-
info: expected
-/
-- #guard_msgs in
-- #eval string_transformer " A b C d E f G "

-- Apps difficulty: introductory
-- Assurance level: unguarded