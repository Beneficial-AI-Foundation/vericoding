/- 
-----Description-----
This task requires writing a Lean 4 method that verifies if every odd index in an array of integers holds an odd number. In other words, for each index in the array that is odd, the number located at that index must also be odd. The method should return true if this condition is satisfied for every odd index; otherwise, it should return false.

-----Input-----
The input consists of:
a: An array of integers.

-----Output-----
The output is a Boolean value:
Returns true if, for every odd index in the array, the corresponding element is odd.
Returns false if there is at least one odd index where the corresponding element is not odd.

-----Note-----
There are no preconditions; the method will work for any array of integers.
-/

@[reducible, simp]
def isOddAtIndexOdd_precond (a : Array Int) : Prop :=
  True

-- <vc-helpers>
def isOdd (n : Int) : Bool :=
  n % 2 == 1
-- </vc-helpers>

def isOddAtIndexOdd (a : Array Int) (h_precond : isOddAtIndexOdd_precond (a)) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def isOddAtIndexOdd_postcond (a : Array Int) (result: Bool) (h_precond : isOddAtIndexOdd_precond (a)) :=
  result ↔ (∀ i, (hi : i < a.size) → isOdd i → isOdd (a[i]))

theorem isOddAtIndexOdd_spec_satisfied (a: Array Int) (h_precond : isOddAtIndexOdd_precond (a)) :
    isOddAtIndexOdd_postcond (a) (isOddAtIndexOdd (a) h_precond) h_precond := by
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
            "a": "#[1, 2, 3, 4, 5]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "a": "#[1, 3, 5, 7, 9]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[2, 4, 6, 8, 10]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "a": "#[]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[7]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[0, 1, 0, 1]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[0, 2, 4, 6]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/