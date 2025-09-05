/- 
-----Description-----
This problem focuses on reversing an array of integers. The goal is to take an input array and produce a new array with the elements arranged in the reverse order.

-----Input-----
The input consists of:
• a: An array of integers, which may be empty, contain one element, or many elements.

-----Output-----
The output is an array of integers that:
• Has the same length as the input array.
• Contains the same elements as the input array, but in reverse order.
• For every valid index i in the input array, the output at index i is equal to the element at index (a.size - 1 - i) from the input array.

-----Note-----
There are no specific preconditions; the method should correctly handle any array of integers.
-/

@[reducible, simp]
def reverse_precond (a : Array Int) : Prop :=
  True

-- <vc-helpers>
def reverse_core (arr : Array Int) (i : Nat) : Array Int :=
  if i < arr.size / 2 then
    let j := arr.size - 1 - i
    let temp := arr[i]!
    let arr' := arr.set! i (arr[j]!)
    let arr'' := arr'.set! j temp
    reverse_core arr'' (i + 1)
  else
    arr
-- </vc-helpers>

def reverse (a : Array Int) (h_precond : reverse_precond (a)) : Array Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def reverse_postcond (a : Array Int) (result: Array Int) (h_precond : reverse_precond (a)) :=
  (result.size = a.size) ∧ (∀ i : Nat, i < a.size → result[i]! = a[a.size - 1 - i]!)

theorem reverse_spec_satisfied (a: Array Int) (h_precond : reverse_precond (a)) :
    reverse_postcond (a) (reverse (a) h_precond) h_precond := by
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
        "expected": "#[5, 4, 3, 2, 1]",
        "unexpected": [
            "#[1, 2, 3, 4, 5]",
            "#[5, 3, 4, 2, 1]",
            "#[2, 3, 4, 5, 6]"
        ]
    },
    {
        "input": {
            "a": "#[10, 20, 30, 40]"
        },
        "expected": "#[40, 30, 20, 10]",
        "unexpected": [
            "#[10, 20, 30, 40]",
            "#[40, 20, 30, 10]",
            "#[30, 20, 10, 40]"
        ]
    },
    {
        "input": {
            "a": "#[]"
        },
        "expected": "#[]",
        "unexpected": [
            "#[0]",
            "#[-1]",
            "#[1]"
        ]
    },
    {
        "input": {
            "a": "#[7]"
        },
        "expected": "#[7]",
        "unexpected": [
            "#[0]",
            "#[7, 7]",
            "#[1]"
        ]
    },
    {
        "input": {
            "a": "#[-1, 0, 1]"
        },
        "expected": "#[1, 0, -1]",
        "unexpected": [
            "#[-1, 0, 1]",
            "#[0, 1, -1]",
            "#[1, -1, 0]"
        ]
    }
]
-/
