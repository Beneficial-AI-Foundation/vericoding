/- 
-----Description-----
The problem is about processing a sequence of integer operations to determine cumulative results and identify potential negative outcomes. Given a list of integers, the task is to generate an array where the first element is 0 and each subsequent element is the cumulative sum of the operations performed sequentially. Additionally, the solution should check whether any of these cumulative values (after the initial 0) is negative, and return a corresponding boolean flag.

-----Input-----
The input consists of:
• operations: A list of integers representing sequential operations.

-----Output-----
The output is a tuple consisting of:
• An array of integers representing the partial sums. The array’s size is one more than the number of operations, starting with 0 and where for each index i such that 0 ≤ i < operations.length, the element at index i+1 is equal to the element at index i added to operations[i].
• A boolean value that is true if there exists an index i (with 1 ≤ i ≤ operations.length) such that the i-th partial sum is negative, and false otherwise.

-----Note-----
The function should also correctly handle an empty list of operations.
-/

@[reducible, simp]
def below_zero_precond (operations : List Int) : Prop :=
  True

-- <vc-helpers>
def buildS (operations : List Int) : Array Int :=
  let sList := operations.foldl
    (fun (acc : List Int) (op : Int) =>
      let last := acc.getLast? |>.getD 0
      acc.append [last + op])
    [0]
  Array.mk sList
-- </vc-helpers>

def below_zero (operations : List Int) (h_precond : below_zero_precond (operations)) : (Array Int × Bool) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def below_zero_postcond (operations : List Int) (result: (Array Int × Bool)) (h_precond : below_zero_precond (operations)) :=
  let s := result.1
  let result := result.2
  s.size = operations.length + 1 ∧
  s[0]? = some 0 ∧
  (List.range (s.size - 1)).all (fun i => s[i + 1]? = some (s[i]! + operations[i]!)) ∧
  ((result = true) → ((List.range (operations.length)).any (fun i => s[i + 1]! < 0))) ∧
  ((result = false) → s.all (· ≥ 0))

theorem below_zero_spec_satisfied (operations: List Int) (h_precond : below_zero_precond (operations)) :
    below_zero_postcond (operations) (below_zero (operations) h_precond) h_precond := by
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
            "operations": "[1, 2, 3]"
        },
        "expected": "(#[0, 1, 3, 6], false)",
        "unexpected": [
            "(#[0, 1, 3, 5], false)",
            "(#[0, 2, 3, 6], false)",
            "(#[0, 1, 3, 6], true)"
        ]
    },
    {
        "input": {
            "operations": "[-1, 2, -1]"
        },
        "expected": "(#[0, -1, 1, 0], true)",
        "unexpected": [
            "(#[0, -1, 1, 0], false)",
            "(#[0, -1, 0, 0], true)",
            "(#[0, -2, 1, 0], true)"
        ]
    },
    {
        "input": {
            "operations": "[]"
        },
        "expected": "(#[0], false)",
        "unexpected": [
            "(#[0], true)",
            "(#[0, 0], false)",
            "(#[0, 1], false)"
        ]
    },
    {
        "input": {
            "operations": "[0, 0, 0]"
        },
        "expected": "(#[0, 0, 0, 0], false)",
        "unexpected": [
            "(#[0, 0, 0, 0], true)",
            "(#[0, 0, 0], false)",
            "(#[0, 0, 1, 0], false)"
        ]
    },
    {
        "input": {
            "operations": "[10, -20, 5]"
        },
        "expected": "(#[0, 10, -10, -5], true)",
        "unexpected": [
            "(#[0, 10, -10, -5], false)",
            "(#[0, 10, -9, -5], true)",
            "(#[0, 10, -10, -6], true)"
        ]
    }
]
-/
