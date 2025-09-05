/- 
-----Description-----
This task requires writing a Lean 4 method that removes an element from a given array of integers at a specified index. The resulting array should contain all the original elements except for the one at the given index. Elements before the removed element remain unchanged, and elements after it are shifted one position to the left.

-----Input-----
The input consists of:
• s: An array of integers.
• k: A natural number representing the index of the element to remove (0-indexed).

-----Output-----
The output is an array of integers that:
• Has a length one less than the input array.
• Contains the same elements as the input array, except that the element at index k is omitted.
• Preserves the original order with elements after the removed element shifted left by one position.

-----Note-----
It is assumed that k is a valid index (0 ≤ k < the length of the array).
-/

@[reducible, simp]
def removeElement_precond (s : Array Int) (k : Nat) : Prop :=
  k < s.size

-- <vc-helpers>
-- </vc-helpers>

def removeElement (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) : Array Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def removeElement_postcond (s : Array Int) (k : Nat) (result: Array Int) (h_precond : removeElement_precond (s) (k)) :=
  result.size = s.size - 1 ∧
  (∀ i, i < k → result[i]! = s[i]!) ∧
  (∀ i, i < result.size → i ≥ k → result[i]! = s[i + 1]!)

theorem removeElement_spec_satisfied (s: Array Int) (k: Nat) (h_precond : removeElement_precond (s) (k)) :
    removeElement_postcond (s) (k) (removeElement (s) (k) h_precond) h_precond := by
-- <vc-proof>
  sorry
-- </vc-proof>

/-
-- Invalid Inputs
[
    {
        "input": {
            "s": "#[1]",
            "k": 2
        }
    }
]
-- Tests
[
    {
        "input": {
            "s": "#[1, 2, 3, 4, 5]",
            "k": 2
        },
        "expected": "#[1, 2, 4, 5]",
        "unexpected": [
            "#[1, 2, 3, 5]",
            "#[1, 3, 4, 5]",
            "#[2, 3, 4, 5]"
        ]
    },
    {
        "input": {
            "s": "#[10, 20, 30, 40]",
            "k": 0
        },
        "expected": "#[20, 30, 40]",
        "unexpected": [
            "#[10, 30, 40]",
            "#[10, 20, 30, 40]",
            "#[20, 30, 40, 0]"
        ]
    },
    {
        "input": {
            "s": "#[10, 20, 30, 40]",
            "k": 3
        },
        "expected": "#[10, 20, 30]",
        "unexpected": [
            "#[20, 30, 40]",
            "#[10, 20, 40]",
            "#[10, 30, 40]"
        ]
    },
    {
        "input": {
            "s": "#[7]",
            "k": 0
        },
        "expected": "#[]",
        "unexpected": [
            "#[7]",
            "#[0]"
        ]
    }
]
-/