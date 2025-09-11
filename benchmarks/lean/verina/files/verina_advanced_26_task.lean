-- <vc-preamble>
@[reducible]
def letterCombinations_precond (digits : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def digitToLetters (c : Char) : List Char :=
  match c with
  | '2' => ['a', 'b', 'c']
  | '3' => ['d', 'e', 'f']
  | '4' => ['g', 'h', 'i']
  | '5' => ['j', 'k', 'l']
  | '6' => ['m', 'n', 'o']
  | '7' => ['p', 'q', 'r', 's']
  | '8' => ['t', 'u', 'v']
  | '9' => ['w', 'x', 'y', 'z']
  | _ => []
-- </vc-helpers>

-- <vc-definitions>
def letterCombinations (digits : String) (h_precond : letterCombinations_precond (digits)) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def letterCombinations_postcond (digits : String) (result: List String) (h_precond : letterCombinations_precond (digits)) : Prop :=
  if digits.isEmpty then
    result = []
  else if digits.toList.any (λ c => ¬(c ∈ ['2','3','4','5','6','7','8','9'])) then
    result = []
  else
    let expected := digits.toList.map digitToLetters |>.foldl (λ acc ls => acc.flatMap (λ s => ls.map (λ c => s ++ String.singleton c)) ) [""]
    result.length = expected.length ∧ result.all (λ s => s ∈ expected) ∧ expected.all (λ s => s ∈ result)

theorem letterCombinations_spec_satisfied (digits: String) (h_precond : letterCombinations_precond (digits)) :
    letterCombinations_postcond (digits) (letterCombinations (digits) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "digits": ""
        },
        "expected": "[]",
        "unexpected": [
            "[\"a\"]",
            "[\"b\"]"
        ]
    },
    {
        "input": {
            "digits": "2"
        },
        "expected": "[\"a\", \"b\", \"c\"]",
        "unexpected": [
            "[\"a\"]",
            "[\"b\"]",
            "[\"c\"]"
        ]
    },
    {
        "input": {
            "digits": "9"
        },
        "expected": "[\"w\", \"x\", \"y\", \"z\"]",
        "unexpected": [
            "[\"w\"]",
            "[\"x\"]",
            "[\"y\"]",
            "[\"z\"]"
        ]
    },
    {
        "input": {
            "digits": "23"
        },
        "expected": "[\"ad\", \"ae\", \"af\", \"bd\", \"be\", \"bf\", \"cd\", \"ce\", \"cf\"]",
        "unexpected": [
            "[\"a\"]",
            "[\"b\"]",
            "[\"c\"]"
        ]
    },
    {
        "input": {
            "digits": "27"
        },
        "expected": "[\"ap\", \"aq\", \"ar\", \"as\", \"bp\", \"bq\", \"br\", \"bs\", \"cp\", \"cq\", \"cr\", \"cs\"]",
        "unexpected": [
            "[\"p\"]",
            "[\"q\"]",
            "[\"r\"]",
            "[\"s\"]"
        ]
    },
    {
        "input": {
            "digits": "0"
        },
        "expected": "[]",
        "unexpected": [
            "[\"a\"]",
            "[\"b\"]"
        ]
    }
]
-/