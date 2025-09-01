/- 
-----Description-----
This task requires writing a Lean 4 method that determines if a given string is a palindrome, ignoring all
non-alphanumeric characters and case differences. For example, the string "A man, a plan, a canal: Panama" should return
true.

-----Input-----
A single string:
s: The string to check for palindrome property.

-----Output-----
A boolean (Bool):
true if s is a palindrome when ignoring non-alphanumeric characters and case. false otherwise.
-/

@[reducible]
def palindromeIgnoreNonAlnum_precond (s : String) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def palindromeIgnoreNonAlnum (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible]
def palindromeIgnoreNonAlnum_postcond (s : String) (result: Bool) (h_precond : palindromeIgnoreNonAlnum_precond (s)) : Prop :=
  let cleaned := s.data.filter (fun c => c.isAlpha || c.isDigit) |>.map Char.toLower
let forward := cleaned
let backward := cleaned.reverse

if result then
  forward = backward
else
  forward ≠ backward

theorem palindromeIgnoreNonAlnum_spec_satisfied (s: String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) :
    palindromeIgnoreNonAlnum_postcond (s) (palindromeIgnoreNonAlnum (s) h_precond) h_precond := by
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
            "s": ""
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "A man, a plan, a canal: Panama"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "race a car"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "s": "No 'x' in Nixon"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "abc!!cba?"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "Hello, world!"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/