@[reducible, simp]
def findMajorityElement_precond (lst : List Int) : Prop :=
  True

-- <vc-helpers>
def countOccurrences (n : Int) (lst : List Int) : Nat :=
  lst.foldl (fun acc x => if x = n then acc + 1 else acc) 0
-- </vc-helpers>

def findMajorityElement (lst : List Int) (h_precond : findMajorityElement_precond (lst)) : Int :=
  sorry

@[reducible, simp]
def findMajorityElement_postcond (lst : List Int) (result: Int) (h_precond : findMajorityElement_precond (lst)) : Prop :=
  let count := fun x => (lst.filter (fun y => y = x)).length
  let n := lst.length
  let majority := count result > n / 2 ∧ lst.all (fun x => count x ≤ n / 2 ∨ x = result)
  (result = -1 → lst.all (count · ≤ n / 2) ∨ majority) ∧
  (result ≠ -1 → majority)

theorem findMajorityElement_spec_satisfied (lst: List Int) (h_precond : findMajorityElement_precond (lst)) :
    findMajorityElement_postcond (lst) (findMajorityElement (lst) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "lst": "[1, 2, 1, 1]"
        },
        "expected": 1,
        "unexpected": [
            2,
            -1
        ]
    },
    {
        "input": {
            "lst": "[1, 2, 3, 4]"
        },
        "expected": -1,
        "unexpected": [
            1,
            2,
            3,
            4
        ]
    },
    {
        "input": {
            "lst": "[2, 2, 2, 2, 3, 3]"
        },
        "expected": 2,
        "unexpected": [
            3,
            -1
        ]
    },
    {
        "input": {
            "lst": "[]"
        },
        "expected": -1,
        "unexpected": [
            0,
            1
        ]
    },
    {
        "input": {
            "lst": "[5, 5, 5, 5, 5, 5]"
        },
        "expected": 5,
        "unexpected": [
            0,
            -1
        ]
    },
    {
        "input": {
            "lst": "[-1, -1, -1, 2, 2]"
        },
        "expected": -1,
        "unexpected": [
            2
        ]
    },
    {
        "input": {
            "lst": "[-3, -3, -3, -3, 1]"
        },
        "expected": -3,
        "unexpected": [
            1,
            -1
        ]
    }
]
-/