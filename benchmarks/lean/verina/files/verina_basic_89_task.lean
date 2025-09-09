@[reducible, simp]
def SetToSeq_precond (s : List Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def SetToSeq (s : List Int) (h_precond : SetToSeq_precond (s)) : List Int :=
  sorry

@[reducible, simp]
def SetToSeq_postcond (s : List Int) (result: List Int) (h_precond : SetToSeq_precond (s)) :=
  -- Contains exactly the elements of the set
  result.all (fun a => a ∈ s) ∧ s.all (fun a => a ∈ result) ∧
  -- All elements are unique in the result
  result.all (fun a => result.count a = 1) ∧
  -- The order of elements in the result is preserved
  List.Pairwise (fun a b => (result.idxOf a < result.idxOf b) → (s.idxOf a < s.idxOf b)) result

theorem SetToSeq_spec_satisfied (s: List Int) (h_precond : SetToSeq_precond (s)) :
    SetToSeq_postcond (s) (SetToSeq (s) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "s": "[1, 2, 2, 3, 1]"
        },
        "expected": "[1, 2, 3]",
        "unexpected": [
            "[1, 3, 2]",
            "[1, 2, 2, 3]",
            "[2, 1, 3]"
        ]
    },
    {
        "input": {
            "s": "[5, 5, 5, 5]"
        },
        "expected": "[5]",
        "unexpected": [
            "[5, 5]",
            "[]",
            "[6]"
        ]
    },
    {
        "input": {
            "s": "[]"
        },
        "expected": "[]",
        "unexpected": [
            "[1]",
            "[2]",
            "[0]"
        ]
    },
    {
        "input": {
            "s": "[11, 22, 33]"
        },
        "expected": "[11, 22, 33]",
        "unexpected": [
            "[33, 22, 11]",
            "[11, 11, 22, 33]",
            "[11, 33]"
        ]
    },
    {
        "input": {
            "s": "[3, 1, 4, 1, 5, 9, 2, 6, 5]"
        },
        "expected": "[3, 1, 4, 5, 9, 2, 6]",
        "unexpected": [
            "[3, 1, 4, 1, 5, 9, 2, 6, 5]",
            "[1, 3, 4, 5, 9, 2, 6]",
            "[3, 1, 4, 5, 9, 6]"
        ]
    }
]
-/