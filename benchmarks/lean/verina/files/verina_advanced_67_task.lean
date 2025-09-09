@[reducible, simp]
def runLengthEncode_precond (s : String) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def runLengthEncode (s : String) (h_precond : runLengthEncode_precond (s)) : List (Char × Nat) :=
  sorry

def decodeRLE (lst : List (Char × Nat)) : String :=
  match lst with
  | [] => ""
  | (ch, cnt) :: tail =>
    let repeated := String.mk (List.replicate cnt ch)
    repeated ++ decodeRLE tail
@[reducible, simp]
def runLengthEncode_postcond (s : String) (result: List (Char × Nat)) (h_precond : runLengthEncode_precond (s)) : Prop :=
  (∀ pair ∈ result, pair.snd > 0) ∧
  (∀ i : Nat, i < result.length - 1 → (result[i]!).fst ≠ (result[i+1]!).fst) ∧
  decodeRLE result = s

theorem runLengthEncode_spec_satisfied (s: String) (h_precond : runLengthEncode_precond (s)) :
    runLengthEncode_postcond (s) (runLengthEncode (s) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "s": ""
        },
        "expected": "[]",
        "unexpected": [
            "[('x', 1)]"
        ]
    },
    {
        "input": {
            "s": "aaa"
        },
        "expected": "[('a', 3)]",
        "unexpected": [
            "[('a', 2), ('b', 3)]"
        ]
    },
    {
        "input": {
            "s": "abbbcccaa"
        },
        "expected": "[('a', 1), ('b', 3), ('c', 3), ('a', 2)]",
        "unexpected": [
            "[('a', 2), ('b', 3), ('c', 3), ('a', 2)]"
        ]
    },
    {
        "input": {
            "s": "xyz"
        },
        "expected": "[('x', 1), ('y', 1), ('z', 1)]",
        "unexpected": [
            "[('x', 3)]",
            "[('z', 1)]"
        ]
    },
    {
        "input": {
            "s": "aabbaa"
        },
        "expected": "[('a', 2), ('b', 2), ('a', 2)]",
        "unexpected": [
            "[('a', 2), ('b', 2), ('a', 3)]"
        ]
    }
]
-/