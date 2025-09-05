/- 
-----Description-----
Given an input string "words_str", this task requires writing a Lean 4 function that reverses the order of its words. A word is defined as a contiguous sequence of non-space characters. The function must remove any extra spaces so that the output string contains words separated by a single space and has no leading or trailing spaces. The characters within each word must stay the same as the original input.

-----Input-----
words_str: A string that may contain leading, trailing, or multiple spaces between words.

-----Output-----
A string with the words from the input reversed, where words are separated by a single space, with no extra spaces at the beginning or end.
-/

@[reducible]
def reverseWords_precond (words_str : String) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def reverseWords (words_str : String) (h_precond : reverseWords_precond (words_str)) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible]
def reverseWords_postcond (words_str : String) (result: String) (h_precond : reverseWords_precond (words_str)) : Prop :=
  ∃ words : List String,
    (words = (words_str.splitOn " ").filter (fun w => w ≠ "")) ∧
    result = String.intercalate " " (words.reverse)

theorem reverseWords_spec_satisfied (words_str: String) (h_precond : reverseWords_precond (words_str)) :
    reverseWords_postcond (words_str) (reverseWords (words_str) h_precond) h_precond := by
-- <vc-proof>
  sorry
-- </vc-proof>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "words_str": "the sky is blue"
        },
        "expected": "blue is sky the",
        "unexpected": [
            "the sky is blue",
            "sky the blue is"
        ]
    },
    {
        "input": {
            "words_str": "  hello world  "
        },
        "expected": "world hello",
        "unexpected": [
            "hello world",
            "worldhello"
        ]
    },
    {
        "input": {
            "words_str": "a good   example"
        },
        "expected": "example good a",
        "unexpected": [
            "a good example",
            "example a good"
        ]
    },
    {
        "input": {
            "words_str": "  Bob    Loves  Alice   "
        },
        "expected": "Alice Loves Bob",
        "unexpected": [
            "Bob Loves Alice",
            "Alice Loves Bob "
        ]
    },
    {
        "input": {
            "words_str": "this lab is interesting"
        },
        "expected": "interesting is lab this",
        "unexpected": [
            "gnitseretni si bal siht"
        ]
    }
]
-/
