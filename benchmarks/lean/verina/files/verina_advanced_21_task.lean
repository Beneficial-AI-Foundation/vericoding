@[reducible, simp]
def isPalindrome_precond (s : String) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def isPalindrome (s : String) (h_precond : isPalindrome_precond (s)) : Bool :=
  sorry

@[reducible, simp]
def isPalindrome_postcond (s : String) (result: Bool) (h_precond : isPalindrome_precond (s)) : Prop :=
  (result → (s.toList == s.toList.reverse)) ∧
  (¬ result → (s.toList ≠ [] ∧ s.toList != s.toList.reverse))

theorem isPalindrome_spec_satisfied (s: String) (h_precond : isPalindrome_precond (s)) :
    isPalindrome_postcond (s) (isPalindrome (s) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "s": "racecar"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "abba"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "abc"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "s": ""
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "a"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    }
]
-/