/- 
-----Description-----
Given a nonempty array of integers and a valid index x (with 1 ≤ x < array size), the task is to identify two key pieces of information. First, determine the maximum value among the first x elements of the array. Second, select an index p within the range [x, array size) that satisfies the following conditions: if there exists an element in the segment starting from index x that is strictly greater than the previously determined maximum, then p should be the index of the first such occurrence; otherwise, p should be set to the last index of the array. The focus of the problem is solely on correctly identifying the maximum and choosing the appropriate index based on these order conditions.

-----Input-----
The input consists of:
• a: An array of integers (assumed to be nonempty).
• x: A natural number (Nat) such that 1 ≤ x < a.size.

-----Output-----
The output is a pair (m, p) where:
• m is the maximum value among the first x elements of the array.
• p is an index in the array, with x ≤ p < a.size, determined based on the ordering condition where a[p] is the first element (from index x onward) that is strictly greater than m. If no such element exists, then p is set to a.size − 1.

-----Note-----
It is assumed that the array a is nonempty and that the parameter x meets the precondition 1 ≤ x < a.size. The function relies on helper functions to compute the maximum among the first x elements and to select the appropriate index p based on the given conditions.
-/

@[reducible, simp]
def onlineMax_precond (a : Array Int) (x : Nat) : Prop :=
  a.size > 0 ∧ x < a.size

-- <vc-helpers>
def findBest (a : Array Int) (x : Nat) (i : Nat) (best : Int) : Int :=
  if i < x then
    let newBest := if a[i]! > best then a[i]! else best
    findBest a x (i + 1) newBest
  else best

def findP (a : Array Int) (x : Nat) (m : Int) (i : Nat) : Nat :=
  if i < a.size then
    if a[i]! > m then i else findP a x m (i + 1)
  else a.size - 1
-- </vc-helpers>

def onlineMax (a : Array Int) (x : Nat) (h_precond : onlineMax_precond (a) (x)) : Int × Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def onlineMax_postcond (a : Array Int) (x : Nat) (result: Int × Nat) (h_precond : onlineMax_precond (a) (x)) :=
  let (m, p) := result;
  (x ≤ p ∧ p < a.size) ∧
  (∀ i, i < x → a[i]! ≤ m) ∧
  (∃ i, i < x ∧ a[i]! = m) ∧
  ((p < a.size - 1) → (∀ i, i < p → a[i]! < a[p]!)) ∧
  ((∀ i, x ≤ i → i < a.size → a[i]! ≤ m) → p = a.size - 1)

theorem onlineMax_spec_satisfied (a: Array Int) (x: Nat) (h_precond : onlineMax_precond (a) (x)) :
    onlineMax_postcond (a) (x) (onlineMax (a) (x) h_precond) h_precond := by
-- <vc-proof>
  sorry
-- </vc-proof>

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[]",
            "x": 2
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "#[3, 7, 5, 2, 9]",
            "x": 3
        },
        "expected": "(7, 4)",
        "unexpected": [
            "(7, 3)",
            "(5, 4)"
        ]
    },
    {
        "input": {
            "a": "#[10, 10, 5, 1]",
            "x": 2
        },
        "expected": "(10, 3)",
        "unexpected": [
            "(10, 2)",
            "(7, 3)"
        ]
    },
    {
        "input": {
            "a": "#[1, 3, 3, 3, 1]",
            "x": 2
        },
        "expected": "(3, 4)",
        "unexpected": [
            "(2, 4)",
            "(3, 3)"
        ]
    },
    {
        "input": {
            "a": "#[5, 4, 4, 6, 2]",
            "x": 2
        },
        "expected": "(5, 3)",
        "unexpected": [
            "(4, 2)",
            "(5, 2)",
            "(6, 3)"
        ]
    },
    {
        "input": {
            "a": "#[2, 8, 7, 7, 7]",
            "x": 3
        },
        "expected": "(8, 4)",
        "unexpected": [
            "(7, 4)",
            "(8, 3)"
        ]
    }
]
-/