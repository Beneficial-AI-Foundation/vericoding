/- 
-----Description-----
This task requires writing a function that processes an array of integers and produces a new array containing only the even numbers from the input. The order of these even numbers should remain the same as in the original array, ensuring that every even number from the input appears in the output and that every element in the output is even.

-----Input-----
The input consists of one parameter:
• arr: An array of integers.

-----Output-----
The output is an array of integers that:
• Contains exactly all even numbers from the input array, preserving their original order.
• Meets the specified conditions that ensure no extraneous (odd or non-existing) elements are returned.

-----Note-----
There are no additional preconditions. The function must adhere to the provided specification which enforces evenness and order preservation for the elements in the output array.
-/

@[reducible, simp]
def FindEvenNumbers_precond (arr : Array Int) : Prop :=
  True

-- <vc-helpers>
def isEven (n : Int) : Bool :=
  n % 2 = 0
-- </vc-helpers>

def FindEvenNumbers (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) : Array Int :=
  sorry

@[reducible, simp]
def FindEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : FindEvenNumbers_precond (arr)) :=
  result.all (fun x => isEven x && x ∈ arr) ∧
  List.Pairwise (fun (x, i) (y, j) => if i < j then arr.idxOf x ≤ arr.idxOf y else true) (result.toList.zipIdx)

theorem FindEvenNumbers_spec_satisfied (arr: Array Int) (h_precond : FindEvenNumbers_precond (arr)) :
    FindEvenNumbers_postcond (arr) (FindEvenNumbers (arr) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "arr": "#[1, 2, 3, 4, 5, 6]"
        },
        "expected": "#[2, 4, 6]",
        "unexpected": [
            "#[2, 4, 5]",
            "#[1, 2, 3, 4]",
            "#[2, 3, 6]"
        ]
    },
    {
        "input": {
            "arr": "#[0, -2, 3, -4, 7]"
        },
        "expected": "#[0, -2, -4]",
        "unexpected": [
            "#[0, 3, -4]",
            "#[0, -2, 3]"
        ]
    },
    {
        "input": {
            "arr": "#[1, 3, 5, 7]"
        },
        "expected": "#[]",
        "unexpected": [
            "#[1]",
            "#[0, 1]"
        ]
    },
    {
        "input": {
            "arr": "#[2, 4, 8, 10]"
        },
        "expected": "#[2, 4, 8, 10]",
        "unexpected": [
            "#[2, 4, 8, 9]",
            "#[2, 4, 8, 10, 12]"
        ]
    },
    {
        "input": {
            "arr": "#[]"
        },
        "expected": "#[]",
        "unexpected": [
            "#[0]",
            "#[1, 2]"
        ]
    }
]
-/