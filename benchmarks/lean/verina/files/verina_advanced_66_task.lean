@[reducible]
def reverseWords_precond (words_str : String) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def reverseWords (words_str : String) (h_precond : reverseWords_precond (words_str)) : String :=
  sorry

@[reducible]
def reverseWords_postcond (words_str : String) (result: String) (h_precond : reverseWords_precond (words_str)) : Prop :=
  ∃ words : List String,
    (words = (words_str.splitOn " ").filter (fun w => w ≠ "")) ∧
    result = String.intercalate " " (words.reverse)

theorem reverseWords_spec_satisfied (words_str: String) (h_precond : reverseWords_precond (words_str)) :
    reverseWords_postcond (words_str) (reverseWords (words_str) h_precond) h_precond := by
  sorry

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